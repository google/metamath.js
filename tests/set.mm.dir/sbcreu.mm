include "wreu.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "sbcex.mm"
include "wrex.mm"
include "reurex.mm"
include "rexlimivw.mm"
include "syl.mm"
include "wsb.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "reubidv.mm"
include "nfcv.mm"
include "nfs1v.mm"
include "nfreu.mm"
include "weq.mm"
include "sbequ12.mm"
include "sbie.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem sbcreu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint ph z
  disjoint B z
  assert |- ( [. A / x ]. E! y e. B ph <-> E! y e. B [. A / x ]. ph )

  proof
    wph
    vy
    cB
    wreu
    #
    vx
    cA
    wsbc
    #
    cA
    cvv
    wcel
    #
    wph
    vx
    cA
    wsbc
    #
    vy
    cB
    wreu
    #
    @0
    vx
    cA
    sbcex
    @4
    @3
    vy
    cB
    wrex
    @2
    @3
    vy
    cB
    reurex
    @3
    @2
    vy
    cB
    wph
    vx
    cA
    sbcex
    rexlimivw
    syl
    @0
    vx
    vz
    wsb
    wph
    vx
    vz
    wsb
    #
    vy
    cB
    wreu
    #
    @1
    @4
    vz
    cA
    cvv
    @0
    vx
    vz
    cA
    dfsbcq2
    vz
    cv
    cA
    wceq
    @5
    @3
    vy
    cB
    wph
    vx
    vz
    cA
    dfsbcq2
    reubidv
    @0
    @6
    vx
    vz
    @5
    vx
    vy
    cB
    vx
    cB
    nfcv
    wph
    vx
    vz
    nfs1v
    nfreu
    vx
    vz
    weq
    wph
    @5
    vy
    cB
    wph
    vx
    vz
    sbequ12
    reubidv
    sbie
    vtoclbg
    pm5.21nii
end
