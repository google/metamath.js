include "ctrg.mm"
include "wcel.mm"
include "ctgp.mm"
include "crg.mm"
include "ctmd.mm"
include "istrg.mm"
include "simp3bi.mm"

theorem trgtmd
  let cR: class R
  let cM: class M
  let vr: setvar r
  let cU: class U
  assume istrg.1: |- M = ( mulGrp ` R )


  assert |- ( R e. TopRing -> M e. TopMnd )

  proof
    cR
    ctrg
    wcel
    cR
    ctgp
    wcel
    cR
    crg
    wcel
    cM
    ctmd
    wcel
    cR
    cM
    istrg.1
    istrg
    simp3bi
end
