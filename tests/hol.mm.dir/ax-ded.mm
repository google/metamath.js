
axiom ax-ded
  let tr: term R
  let ts: term S
  let tt: term T
  assume ax-ded.1: |- ( R , S ) |= T
  assume ax-ded.2: |- ( R , T ) |= S
  assert |- R |= ( ( = S ) T )
end
