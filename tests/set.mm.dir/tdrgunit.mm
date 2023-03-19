include "ctdrg.mm"
include "wcel.mm"
include "ctrg.mm"
include "cdr.mm"
include "cress.mm"
include "co.mm"
include "ctgp.mm"
include "istdrg.mm"
include "simp3bi.mm"

theorem tdrgunit
  let cR: class R
  let cU: class U
  let cM: class M
  let vr: setvar r
  assume istrg.1: |- M = ( mulGrp ` R )
  assume istdrg.1: |- U = ( Unit ` R )


  assert |- ( R e. TopDRing -> ( M |`s U ) e. TopGrp )

  proof
    cR
    ctdrg
    wcel
    cR
    ctrg
    wcel
    cR
    cdr
    wcel
    cM
    cU
    cress
    co
    ctgp
    wcel
    cR
    cU
    cM
    istrg.1
    istdrg.1
    istdrg
    simp3bi
end
