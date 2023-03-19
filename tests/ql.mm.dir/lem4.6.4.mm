include "u1lem12.mm"

theorem lem4.6.4
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->1 b ) ->1 b ) = ( a ' ->1 b )

  proof
    wva
    wvb
    u1lem12
end
