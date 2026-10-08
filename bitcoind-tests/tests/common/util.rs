use simplicityhl::elements::secp256k1_zkp as secp256k1;

pub fn key_pair(secret_key: u32) -> secp256k1::Keypair {
    let mut secret_key_bytes = [0u8; 32];
    secret_key_bytes[28..].copy_from_slice(&secret_key.to_be_bytes());
    secp256k1::Keypair::from_seckey_slice(secp256k1::SECP256K1, &secret_key_bytes)
        .expect("secret key should be valid")
}

pub fn sign_schnorr(secret_key: u32, message: [u8; 32]) -> [u8; 64] {
    let key_pair = key_pair(secret_key);
    let message = secp256k1::Message::from_digest(message);
    secp256k1::SECP256K1
        .sign_schnorr_no_aux_rand(&message, &key_pair)
        .serialize()
}

pub fn xonly_public_key(secret_key: u32) -> simplicityhl::num::U256 {
    let key_pair = key_pair(secret_key);
    let bytes = key_pair.x_only_public_key().0.serialize();
    simplicityhl::num::U256::from_byte_array(bytes)
}
