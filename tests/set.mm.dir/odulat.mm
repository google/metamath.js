include "clat.mm"
include "wcel.mm"
include "odulatb.mm"
include "ibi.mm"

theorem odulat
  let cD: class D
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cL: class L
  let cU: class U
  let cV: class V
  let c.or: class .\/
  let c.an: class ./\
  assume oduglb.d: |- D = ( ODual ` O )


  assert |- ( O e. Lat -> D e. Lat )

  proof
    cO
    clat
    wcel
    cD
    clat
    wcel
    cD
    cO
    clat
    oduglb.d
    odulatb
    ibi
end
