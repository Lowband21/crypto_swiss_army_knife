use num::bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use requestty::{prompt, Question};

fn main() {
    let question = vec![Question::select("task")
        .message("Choose a task:")
        .choice("Encryption/decryption of shift cipher")
        .choice("Encryption/decryption of affine cipher")
        .choice("Computation of index of coincidence and mutual index of coincidence")
        .choice("GCD of two numbers (iterative or recursive)")
        .choice("Computing inverses mod n using the extended euclidean algorithm")
        .choice("Solve a system of congruences mod n (using CRT)")
        .choice("Exponentiation mod p (using square and multiply)")
        .build()];

    let answers = prompt(question).unwrap();

    let task: String = answers
        .get("task")
        .unwrap()
        .as_list_item()
        .unwrap()
        .clone()
        .text;

    match task.as_str() {
        "Encryption/decryption of shift cipher" => {
            // Ask user if they want to encrypt or decrypt
            let choice_question = Question::select("choice")
                .message("Do you want to encrypt or decrypt?")
                .choice("encrypt")
                .choice("decrypt")
                .build();
            let choice_answer = prompt(vec![choice_question]).unwrap();

            let choice: String = choice_answer
                .get("choice")
                .unwrap()
                .as_list_item()
                .unwrap()
                .clone()
                .text;

            // Ask user for shift value
            let shift_question = Question::input("shift")
                .message("Enter the shift value:")
                .validate(|input, _| {
                    if input.parse::<i32>().is_err() {
                        Err(String::from("Please enter a number"))
                    } else {
                        Ok(())
                    }
                })
                .build();

            let shift_answer = prompt(vec![shift_question]).unwrap();
            let shift: i32 = shift_answer
                .get("shift")
                .unwrap()
                .as_string()
                .unwrap()
                .parse::<i32>()
                .unwrap();

            // Ask user for message to encrypt or decrypt
            let message_question = Question::input("message")
                .message("Enter the message to encrypt or decrypt:")
                .validate(|input, _| {
                    if input.is_empty() {
                        Err(String::from("This field cannot be empty"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let message_answer = prompt(vec![message_question]).unwrap();
            let message: String = message_answer
                .get("message")
                .unwrap()
                .as_string()
                .unwrap()
                .to_string();

            // Encrypt/Decrypt
            let result = if choice == "encrypt" {
                encrypt_shift_cipher(message, shift)
            } else {
                decrypt_shift_cipher(message, shift)
            };

            //Return cyphertext/plaintext
            println!("Result: {}", result);
        }
        "Encryption/decryption of affine cipher" => {
            // Ask user if they want to encrypt or decrypt
            let choice_question = Question::select("choice")
                .message("Do you want to encrypt or decrypt?")
                .choice("encrypt")
                .choice("decrypt")
                .build();
            let choice_answer = prompt(vec![choice_question]).unwrap();
            let choice: String = choice_answer
                .get("choice")
                .unwrap()
                .as_list_item()
                .unwrap()
                .clone()
                .text;

            // Ask user for shift value
            let shift_question = Question::input("shift")
                .message("Enter the shift value:")
                .validate(|input, _| {
                    if input.parse::<i32>().is_err() {
                        Err(String::from("Please enter a number"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let shift_answer = prompt(vec![shift_question]).unwrap();
            let shift: i32 = shift_answer
                .get("shift")
                .unwrap()
                .as_string()
                .unwrap()
                .parse::<i32>()
                .unwrap();

            // Ask user for multiplier value
            let multiplier_question = Question::input("multiplier")
                .message("Enter the multiplier value:")
                .validate(|input, _| {
                    if input.parse::<i32>().is_err() {
                        Err(String::from("Please enter a number"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let multiplier_answer = prompt(vec![multiplier_question]).unwrap();
            let multiplier: i32 = multiplier_answer
                .get("multiplier")
                .unwrap()
                .as_string()
                .unwrap()
                .parse::<i32>()
                .unwrap();

            // Ask user for message to encrypt or decrypt
            let message_question = Question::input("message")
                .message("Enter the message to encrypt or decrypt:")
                .validate(|input, _| {
                    if input.is_empty() {
                        Err(String::from("This field cannot be empty"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let message_answer = prompt(vec![message_question]).unwrap();
            let message: String = message_answer
                .get("message")
                .unwrap()
                .as_string()
                .unwrap()
                .to_string();

            // Encrypt/Decrypt
            let result = if choice == "encrypt" {
                encrypt_affine_cipher(message, shift, multiplier)
            } else {
                decrypt_affine_cipher(message, shift, multiplier)
            };

            //Return cyphertext/plaintext
            println!("Result: {}", result);
        }
        "Computation of index of coincidence and mutual index of coincidence" => {
            // Ask user for first text
            let text1_question = Question::input("text1")
                .message("Enter the first text:")
                .validate(|input, _| {
                    if input.is_empty() {
                        Err(String::from("This field cannot be empty"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let text1_answer = prompt(vec![text1_question]).unwrap();
            let text1: String = text1_answer
                .get("text1")
                .unwrap()
                .as_string()
                .unwrap()
                .to_string();

            // Ask user for second text
            let text2_question = Question::input("text2")
                .message("Enter the second text:")
                .validate(|input, _| {
                    if input.is_empty() {
                        Err(String::from("This field cannot be empty"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let text2_answer = prompt(vec![text2_question]).unwrap();
            let text2: String = text2_answer
                .get("text2")
                .unwrap()
                .as_string()
                .unwrap()
                .to_string();

            // Compute IC and MIC
            let ic1 = compute_index_of_coincidence(&text1);
            let ic2 = compute_index_of_coincidence(&text2);
            let mic = compute_mutual_index_of_coincidence(&text1, &text2);

            // Print IC and MIC
            println!("Index of Coincidence for first text: {}", ic1);
            println!("Index of Coincidence for second text: {}", ic2);
            println!("Mutual Index of Coincidence: {}", mic);
        }
        "GCD of two numbers (iterative or recursive)" => {
            // Ask user if they want to use iterative or recursive method
            let method_question = Question::select("method")
                .message("Do you want to use iterative or recursive method?")
                .choice("iterative")
                .choice("recursive")
                .build();
            let method_answer = prompt(vec![method_question]).unwrap();

            let method: String = method_answer
                .get("method")
                .unwrap()
                .as_list_item()
                .unwrap()
                .clone()
                .text;

            // Ask user for first number
            let num1_question = Question::input("num1")
                .message("Enter the first number:")
                .validate(|input, _| {
                    if input.parse::<i32>().is_err() {
                        Err(String::from("Please enter a number"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let num1_answer = prompt(vec![num1_question]).unwrap();
            let num1: i32 = num1_answer
                .get("num1")
                .unwrap()
                .as_string()
                .unwrap()
                .parse::<i32>()
                .unwrap();

            // Ask user for second number
            let num2_question = Question::input("num2")
                .message("Enter the second number:")
                .validate(|input, _| {
                    if input.parse::<i32>().is_err() {
                        Err(String::from("Please enter a number"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let num2_answer = prompt(vec![num2_question]).unwrap();
            let num2: i32 = num2_answer
                .get("num2")
                .unwrap()
                .as_string()
                .unwrap()
                .parse::<i32>()
                .unwrap();

            // Compute GCD
            let gcd = if method == "iterative" {
                gcd_iterative(num1, num2)
            } else {
                gcd_recursive(num1, num2)
            };

            // Print GCD
            println!("The GCD of {} and {} is: {}", num1, num2, gcd);
        }
        "Computing inverses mod n using the extended euclidean algorithm" => {
            // Ask user for number
            let num_question = Question::input("num")
                .message("Enter the number:")
                .validate(|input, _| {
                    if input.parse::<BigInt>().is_err() {
                        Err(String::from("Please enter a valid number"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let num_answer = prompt(vec![num_question]).unwrap();
            let num: BigInt = num_answer
                .get("num")
                .unwrap()
                .as_string()
                .unwrap()
                .parse::<BigInt>()
                .unwrap();

            // Ask user for modulus
            let mod_question = Question::input("mod")
                .message("Enter the modulus:")
                .validate(|input, _| {
                    if input.parse::<BigInt>().is_err() {
                        Err(String::from("Please enter a valid number"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let mod_answer = prompt(vec![mod_question]).unwrap();
            let modulus: BigInt = mod_answer
                .get("mod")
                .unwrap()
                .as_string()
                .unwrap()
                .parse::<BigInt>()
                .unwrap();

            // Compute inverse mod n
            let (_, x, _) = extended_gcd_bigint(&num, &modulus);
            let inverse = x % &modulus;

            // Print the inverse mod n
            println!("The inverse of {} mod {} is: {}", num, modulus, inverse);
        }
        "Solve a system of congruences mod n (using CRT)" => {
            // Ask user for list of moduli
            let moduli_question = Question::input("moduli")
                .message("Enter the moduli as comma separated numbers:")
                .validate(|input, _| {
                    if input.is_empty() {
                        Err(String::from("This field cannot be empty"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let moduli_answer = prompt(vec![moduli_question]).unwrap();
            let moduli: Vec<BigInt> = moduli_answer
                .get("moduli")
                .unwrap()
                .as_string()
                .unwrap()
                .split(',')
                .map(|s| s.trim().parse().expect("Parse error"))
                .collect();

            // Ask user for list of remainders
            let remainders_question = Question::input("remainders")
                .message("Enter the remainders as comma separated numbers:")
                .validate(|input, _| {
                    if input.is_empty() {
                        Err(String::from("This field cannot be empty"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let remainders_answer = prompt(vec![remainders_question]).unwrap();
            let remainders: Vec<BigInt> = remainders_answer
                .get("remainders")
                .unwrap()
                .as_string()
                .unwrap()
                .split(',')
                .map(|s| s.trim().parse().expect("Parse error"))
                .collect();

            // Ensure moduli and remainders are of the same length
            if moduli.len() != remainders.len() {
                println!("Error: moduli and remainders must have the same length.");
                return;
            }

            // Solve system using CRT
            let solution = solve_system_crt(&moduli, &remainders);

            println!("Solution: {}", solution);
        }
        "Exponentiation mod p (using square and multiply)" => {
            // Ask user for base
            let base_question = Question::input("base")
                .message("Enter the base:")
                .validate(|input, _| {
                    if input.parse::<BigUint>().is_err() {
                        Err(String::from("Please enter a number"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let base_answer = prompt(vec![base_question]).unwrap();
            let base: BigUint = base_answer
                .get("base")
                .unwrap()
                .as_string()
                .unwrap()
                .parse::<BigUint>()
                .unwrap();

            // Ask user for exponent
            let exponent_question = Question::input("exponent")
                .message("Enter the exponent:")
                .validate(|input, _| {
                    if input.parse::<BigUint>().is_err() {
                        Err(String::from("Please enter a number"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let exponent_answer = prompt(vec![exponent_question]).unwrap();
            let exponent: BigUint = exponent_answer
                .get("exponent")
                .unwrap()
                .as_string()
                .unwrap()
                .parse::<BigUint>()
                .unwrap();

            // Ask user for modulus
            let modulus_question = Question::input("modulus")
                .message("Enter the modulus:")
                .validate(|input, _| {
                    if input.parse::<BigUint>().is_err() {
                        Err(String::from("Please enter a number"))
                    } else {
                        Ok(())
                    }
                })
                .build();
            let modulus_answer = prompt(vec![modulus_question]).unwrap();
            let modulus: BigUint = modulus_answer
                .get("modulus")
                .unwrap()
                .as_string()
                .unwrap()
                .parse::<BigUint>()
                .unwrap();

            // Calculate mod exp
            let result = mod_exp(base, exponent, modulus);

            // Output the result
            println!("Result: {}", result);
        }
        _ => println!("Invalid option!"),
    }
}

fn encrypt_shift_cipher(text: String, shift: i32) -> String {
    text.chars()
        .map(|c| {
            if c.is_ascii_alphabetic() {
                let base = if c.is_ascii_lowercase() { 'a' } else { 'A' };
                let offset = (c as i32 - base as i32 + shift) % 26;
                std::char::from_u32((base as u32) + offset as u32).unwrap()
            } else {
                c
            }
        })
        .collect()
}

fn decrypt_shift_cipher(text: String, shift: i32) -> String {
    text.chars()
        .map(|c| {
            if c.is_ascii_alphabetic() {
                let base = if c.is_ascii_lowercase() { 'a' } else { 'A' };
                let offset = (c as i32 - base as i32 - shift + 26) % 26;
                std::char::from_u32((base as u32) + offset as u32).unwrap()
            } else {
                c
            }
        })
        .collect()
}

fn encrypt_affine_cipher(message: String, shift: i32, multiplier: i32) -> String {
    let m = 26; // English alphabet
    message
        .chars()
        .map(|c| {
            if c.is_ascii_lowercase() {
                let x = c as i32 - 'a' as i32;
                let y = (multiplier * x + shift) % m;
                (y + 'a' as i32) as u8 as char
            } else {
                c
            }
        })
        .collect()
}

fn decrypt_affine_cipher(message: String, shift: i32, multiplier: i32) -> String {
    let m = 26; // English alphabet
    let multiplier_inv =
        mod_inverse(multiplier, m).expect("Multiplier has no inverse, cannot decrypt!");

    message
        .chars()
        .map(|c| {
            if c.is_ascii_lowercase() {
                let y = c as i32 - 'a' as i32;
                let x = (multiplier_inv * (y - shift)).rem_euclid(m);
                (x + 'a' as i32) as u8 as char
            } else {
                c
            }
        })
        .collect()
}

fn mod_inverse(a: i32, m: i32) -> Option<i32> {
    let (g, x, _) = extended_gcd(a, m);
    if g == 1 {
        Some((x % m + m) % m)
    } else {
        None
    }
}

fn extended_gcd(a: i32, b: i32) -> (i32, i32, i32) {
    if a == 0 {
        (b, 0, 1)
    } else {
        let (g, x, y) = extended_gcd(b % a, a);
        (g, y - (b / a) * x, x)
    }
}

fn compute_index_of_coincidence(text: &str) -> f64 {
    let mut freqs = [0; 26];
    let mut count = 0;
    for c in text.chars() {
        if let Some(i) = c.to_digit(36) {
            let i = i as usize;
            if i >= 10 {
                freqs[i - 10] += 1;
                count += 1;
            }
        }
    }
    let count = count as f64;
    freqs
        .iter()
        .map(|&n| {
            let n = n as f64;
            n * (n - 1.0)
        })
        .sum::<f64>()
        / (count * (count - 1.0))
}

fn compute_mutual_index_of_coincidence(text1: &str, text2: &str) -> f64 {
    let mut freqs1 = [0; 26];
    let mut freqs2 = [0; 26];
    let mut count1 = 0;
    let mut count2 = 0;
    for c in text1.chars() {
        if let Some(i) = c.to_digit(36) {
            let i = i as usize;
            if i >= 10 {
                freqs1[i - 10] += 1;
                count1 += 1;
            }
        }
    }
    for c in text2.chars() {
        if let Some(i) = c.to_digit(36) {
            let i = i as usize;
            if i >= 10 {
                freqs2[i - 10] += 1;
                count2 += 1;
            }
        }
    }
    let count1 = count1 as f64;
    let count2 = count2 as f64;
    freqs1
        .iter()
        .zip(freqs2.iter())
        .map(|(&n1, &n2)| {
            let n1 = n1 as f64;
            let n2 = n2 as f64;
            n1 * n2
        })
        .sum::<f64>()
        / (count1 * count2)
}

fn gcd_iterative(mut a: i32, mut b: i32) -> i32 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a.abs()
}

fn gcd_recursive(a: i32, b: i32) -> i32 {
    if b == 0 {
        a.abs()
    } else {
        gcd_recursive(b, a % b)
    }
}

fn extended_gcd_bigint(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
    if *a == BigInt::zero() {
        (b.clone(), BigInt::zero(), BigInt::one())
    } else {
        let (g, x, y) = extended_gcd_bigint(&(b % a), a);
        (g, y.clone() - (b / a) * x.clone(), x)
    }
}

fn solve_system_crt(moduli: &Vec<BigInt>, remainders: &Vec<BigInt>) -> BigInt {
    let product: BigInt = moduli.iter().product();

    let mut sum = BigInt::zero();

    for (&ref modulus, &ref remainder) in moduli.iter().zip(remainders) {
        let partial_product = &product / modulus;

        let (_, inv_modulus, _) = extended_gcd_bigint(&partial_product, &modulus);

        sum += remainder * partial_product * inv_modulus;
    }

    sum % product
}

pub fn mod_exp(mut base: BigUint, mut exponent: BigUint, modulus: BigUint) -> BigUint {
    let mut result: BigUint = if exponent.is_zero() {
        Zero::zero()
    } else {
        One::one()
    };
    base = base % modulus.clone();

    // Keep squaring the base and reducing the exponent until the exponent becomes zero
    while !exponent.is_zero() {
        if &exponent % 2u8 == 1u8.into() {
            result = (result * &base) % &modulus;
        }
        base = (&base * &base) % &modulus;
        exponent >>= 1;
    }

    result
}
