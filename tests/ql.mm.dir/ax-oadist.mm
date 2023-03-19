
axiom ax-oadist
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e
  let wvf: term f
  let wvh: term h
  let wvj: term j
  let wvk: term k
  assume oad.1: |- e = ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) )
  assume oad.2: |- f = ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v e )
  assume oad.3: |- h =< ( a ->1 d )
  assume oad.4: |- j =< f
  assume oad.5: |- k =< f
  assume oad.6: |- ( h ^ ( b ->1 d ) ) =< k
  assert |- ( h ^ ( j v k ) ) = ( ( h ^ j ) v ( h ^ k ) )
end
