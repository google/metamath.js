include "chmph.mm"
include "wbr.mm"
include "chmeo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cen.mm"
include "hmph.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "ctop.mm"
include "cima.mm"
include "cmpt.mm"
include "wf1o.mm"
include "ccn.mm"
include "hmeocn.mm"
include "cntop1.mm"
include "syl.mm"
include "cntop2.mm"
include "eqid.mm"
include "hmeoimaf1o.mm"
include "f1oen2g.mm"
include "syl3anc.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem hmphen
  let cJ: class J
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let cL: class L


  assert |- ( J ~= K -> J ~~ K )

  proof
    cJ
    cK
    chmph
    wbr
    cJ
    cK
    chmeo
    co
    #
    c0
    wne
    #
    cJ
    cK
    cen
    wbr
    #
    cJ
    cK
    hmph
    @1
    vf
    cv
    #
    @0
    wcel
    #
    vf
    wex
    @2
    vf
    @0
    n0
    @4
    @2
    vf
    @4
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    cJ
    cK
    vx
    cJ
    @3
    vx
    cv
    cima
    cmpt
    #
    wf1o
    @2
    @4
    @3
    cJ
    cK
    ccn
    co
    wcel
    #
    @5
    @3
    cJ
    cK
    hmeocn
    #
    @3
    cJ
    cK
    cntop1
    syl
    @4
    @8
    @6
    @9
    @3
    cJ
    cK
    cntop2
    syl
    vx
    @3
    @7
    cJ
    cK
    @7
    eqid
    hmeoimaf1o
    cJ
    cK
    @7
    ctop
    ctop
    f1oen2g
    syl3anc
    exlimiv
    sylbi
    sylbi
end
