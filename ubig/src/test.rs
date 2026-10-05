use crate::priv_prelude::*;

pub fn random_usize(rng: &mut impl RngExt) -> usize {
    cfg_select! {
        target_pointer_width = "16" => {
            rng.random::<u16>() as usize
        },
        target_pointer_width = "32" => {
            rng.random::<u32>() as usize
        },
        target_pointer_width = "64" => {
            rng.random::<u64>() as usize
        },
        _ => {
            compile_error!("unsupported target_pointer_width")
        },
    }
}

