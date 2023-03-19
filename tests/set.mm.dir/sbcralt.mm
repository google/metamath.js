include "wral.mm"
include "wsbc.mm"
include "cv.mm"
include "wcel.mm"
include "wnfc.mm"
include "wa.mm"
include "sbcco.mm"
include "simpl.mm"
include "wsb.mm"
include "wceq.mm"
include "sbsbc.mm"
include "nfcv.mm"
include "nfs1v.mm"
include "nfral.mm"
include "weq.mm"
include "sbequ12.mm"
include "ralbidv.mm"
include "sbie.mm"
include "bitr3i.mm"
include "wb.mm"
include "nfnfc1.mm"
include "nfcvd.mm"
include "id.mm"
include "nfeqd.mm"
include "nfan1.mm"
include "dfsbcq2.mm"
include "adantl.mm"
include "ralbid.mm"
include "adantll.mm"
include "syl5bb.mm"
include "sbcied.mm"
include "syl5bbr.mm"

theorem sbcralt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vz: setvar z

  disjoint x y
  disjoint B x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint V z
  disjoint ph z
  assert |- ( ( A e. V /\ F/_ y A ) -> ( [. A / x ]. A. y e. B ph <-> A. y e. B [. A / x ]. ph ) )

  proof
    wph
    vy
    cB
    wral
    #
    vx
    cA
    wsbc
    @0
    vx
    vz
    cv
    #
    wsbc
    #
    vz
    cA
    wsbc
    cA
    cV
    wcel
    #
    vy
    cA
    wnfc
    #
    wa
    #
    wph
    vx
    cA
    wsbc
    #
    vy
    cB
    wral
    #
    @0
    vx
    vz
    cA
    sbcco
    @5
    @2
    @7
    vz
    cA
    cV
    @3
    @4
    simpl
    @2
    wph
    vx
    vz
    wsb
    #
    vy
    cB
    wral
    #
    @5
    @1
    cA
    wceq
    #
    wa
    @7
    @2
    @0
    vx
    vz
    wsb
    @9
    @0
    vx
    vz
    sbsbc
    @0
    @9
    vx
    vz
    @8
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
    nfral
    vx
    vz
    weq
    wph
    @8
    vy
    cB
    wph
    vx
    vz
    sbequ12
    ralbidv
    sbie
    bitr3i
    @4
    @10
    @9
    @7
    wb
    @3
    @4
    @10
    wa
    @8
    @6
    vy
    cB
    @4
    @10
    vy
    vy
    cA
    nfnfc1
    @4
    vy
    @1
    cA
    @4
    vy
    @1
    nfcvd
    @4
    id
    nfeqd
    nfan1
    @10
    @8
    @6
    wb
    @4
    wph
    vx
    vz
    cA
    dfsbcq2
    adantl
    ralbid
    adantll
    syl5bb
    sbcied
    syl5bbr
end
