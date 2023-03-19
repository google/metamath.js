include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "wne.mm"
include "wn.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "clt.mm"
include "wrex.mm"
include "cn.mm"
include "wss.mm"
include "nnssz.mm"
include "cr.mm"
include "zcn.mm"
include "abscld.mm"
include "arch.mm"
include "syl.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "wb.mm"
include "zre.mm"
include "ltnle.mm"
include "syl2an.mm"
include "rexbidva.mm"
include "rexnal.mm"
include "syl6bb.mm"
include "mpbid.mm"
include "adantl.mm"
include "wi.mm"
include "ralim.mm"
include "dvdsleabs.mm"
include "3expb.mm"
include "expcom.mm"
include "ralrimiv.mm"
include "syl11.mm"
include "expdimp.mm"
include "mtod.mm"
include "nne.mm"
include "sylib.mm"
include "dvds0.mm"
include "breq2.mm"
include "syl5ibr.mm"
include "impbid1.mm"

theorem alzdvds
  let vx: setvar x
  let cN: class N
  let cA: class A
  let cB: class B

  disjoint N x
  disjoint A x
  disjoint B x
  assert |- ( N e. ZZ -> ( A. x e. ZZ x || N <-> N = 0 ) )

  proof
    cN
    cz
    wcel
    #
    vx
    cv
    #
    cN
    cdvds
    wbr
    #
    vx
    cz
    wral
    #
    cN
    cc0
    wceq
    #
    @3
    @0
    @4
    @3
    @0
    wa
    #
    cN
    cc0
    wne
    #
    wn
    @4
    @5
    @6
    @1
    cN
    cabs
    cfv
    #
    cle
    wbr
    #
    vx
    cz
    wral
    #
    @0
    @9
    wn
    #
    @3
    @0
    @7
    @1
    clt
    wbr
    #
    vx
    cz
    wrex
    #
    @10
    cn
    cz
    wss
    @0
    @11
    vx
    cn
    wrex
    #
    @12
    nnssz
    @0
    @7
    cr
    wcel
    #
    @13
    @0
    cN
    cN
    zcn
    abscld
    #
    @7
    vx
    arch
    syl
    @11
    vx
    cn
    cz
    ssrexv
    mpsyl
    @0
    @12
    @8
    wn
    #
    vx
    cz
    wrex
    @10
    @0
    @11
    @16
    vx
    cz
    @0
    @14
    @1
    cr
    wcel
    @11
    @16
    wb
    @1
    cz
    wcel
    #
    @15
    @1
    zre
    @7
    @1
    ltnle
    syl2an
    rexbidva
    @8
    vx
    cz
    rexnal
    syl6bb
    mpbid
    adantl
    @3
    @0
    @6
    @9
    @2
    @8
    wi
    #
    vx
    cz
    wral
    @3
    @9
    @0
    @6
    wa
    #
    @2
    @8
    vx
    cz
    ralim
    @19
    @18
    vx
    cz
    @17
    @19
    @18
    @17
    @0
    @6
    @18
    @1
    cN
    dvdsleabs
    3expb
    expcom
    ralrimiv
    syl11
    expdimp
    mtod
    cN
    cc0
    nne
    sylib
    expcom
    @4
    @2
    vx
    cz
    @17
    @2
    @4
    @1
    cc0
    cdvds
    wbr
    @1
    dvds0
    cN
    cc0
    @1
    cdvds
    breq2
    syl5ibr
    ralrimiv
    impbid1
end
