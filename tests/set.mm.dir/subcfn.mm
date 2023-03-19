include "chomf.mm"
include "cfv.mm"
include "eqid.mm"
include "subcssc.mm"
include "sscfn1.mm"

theorem subcfn
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume subcixp.1: |- ( ph -> J e. ( Subcat ` C ) )
  assume subcfn.2: |- ( ph -> S = dom dom J )


  assert |- ( ph -> J Fn ( S X. S ) )

  proof
    wph
    cS
    cJ
    cC
    chomf
    cfv
    #
    wph
    cC
    @0
    cJ
    subcixp.1
    @0
    eqid
    subcssc
    subcfn.2
    sscfn1
end
