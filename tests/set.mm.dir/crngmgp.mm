include "ccrg.mm"
include "wcel.mm"
include "crg.mm"
include "ccmn.mm"
include "iscrng.mm"
include "simprbi.mm"

theorem crngmgp
  let cR: class R
  let cG: class G
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ringmgp.g: |- G = ( mulGrp ` R )


  assert |- ( R e. CRing -> G e. CMnd )

  proof
    cR
    ccrg
    wcel
    cR
    crg
    wcel
    cG
    ccmn
    wcel
    cR
    cG
    ringmgp.g
    iscrng
    simprbi
end
