include "c1.mm"
include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cprod.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "1re.mm"
include "rexri.mm"
include "a1i.mm"
include "pnfxr.mm"
include "cc.mm"
include "wss.mm"
include "cr.mm"
include "icossre.mm"
include "mp2an.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cv.mm"
include "wa.mm"
include "cmul.mm"
include "sseli.mm"
include "adantr.mm"
include "adantl.mm"
include "remulcld.mm"
include "rexrd.mm"
include "wceq.mm"
include "1t1e1.mm"
include "eqcomi.mm"
include "cc0.mm"
include "0le1.mm"
include "id.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "lemul12ad.mm"
include "eqbrtrd.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "clt.mm"
include "w3a.mm"
include "1le1.mm"
include "ltpnf.mm"
include "ax-mp.mm"
include "3pm3.2i.mm"
include "wb.mm"
include "elico2.mm"
include "mpbir.mm"
include "fprodcllemf.mm"

theorem fprodge1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fprodge1.ph: |- F/ k ph
  assume fprodge1.a: |- ( ph -> A e. Fin )
  assume fprodge1.b: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume fprodge1.ge: |- ( ( ph /\ k e. A ) -> 1 <_ B )

  disjoint A k
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> 1 <_ prod_ k e. A B )

  proof
    wph
    c1
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cA
    cB
    vk
    cprod
    #
    c1
    cpnf
    cico
    co
    #
    wcel
    c1
    @2
    cle
    wbr
    @0
    wph
    c1
    1re
    rexri
    #
    a1i
    @1
    wph
    pnfxr
    a1i
    wph
    vx
    vy
    cA
    cB
    @3
    vk
    fprodge1.ph
    @3
    cc
    wss
    wph
    @3
    cr
    cc
    c1
    cr
    wcel
    #
    @1
    @3
    cr
    wss
    1re
    pnfxr
    c1
    cpnf
    icossre
    mp2an
    #
    ax-resscn
    sstri
    a1i
    vx
    cv
    #
    @3
    wcel
    #
    vy
    cv
    #
    @3
    wcel
    #
    wa
    #
    @7
    @9
    cmul
    co
    #
    @3
    wcel
    wph
    @11
    c1
    cpnf
    @12
    @0
    @11
    @4
    a1i
    @1
    @11
    pnfxr
    a1i
    @11
    @12
    @11
    @7
    @9
    @8
    @7
    cr
    wcel
    @10
    @3
    cr
    @7
    @6
    sseli
    adantr
    #
    @10
    @9
    cr
    wcel
    @8
    @3
    cr
    @9
    @6
    sseli
    adantl
    #
    remulcld
    #
    rexrd
    @11
    c1
    c1
    c1
    cmul
    co
    #
    @12
    cle
    c1
    @16
    wceq
    @11
    @16
    c1
    1t1e1
    eqcomi
    a1i
    @11
    c1
    @7
    c1
    @9
    @5
    @11
    1re
    a1i
    #
    @13
    @17
    @14
    cc0
    c1
    cle
    wbr
    @11
    0le1
    a1i
    #
    @18
    @8
    c1
    @7
    cle
    wbr
    #
    @10
    @8
    @0
    @1
    @8
    @19
    @0
    @8
    @4
    a1i
    @1
    @8
    pnfxr
    a1i
    @8
    id
    c1
    cpnf
    @7
    icogelb
    syl3anc
    adantr
    @10
    c1
    @9
    cle
    wbr
    #
    @8
    @10
    @0
    @1
    @10
    @20
    @0
    @10
    @4
    a1i
    @1
    @10
    pnfxr
    a1i
    @10
    id
    c1
    cpnf
    @9
    icogelb
    syl3anc
    adantl
    lemul12ad
    eqbrtrd
    @11
    @12
    @15
    ltpnfd
    elicod
    adantl
    fprodge1.a
    wph
    vk
    cv
    cA
    wcel
    wa
    #
    c1
    cpnf
    cB
    @0
    @21
    @4
    a1i
    @1
    @21
    pnfxr
    a1i
    @21
    cB
    fprodge1.b
    rexrd
    fprodge1.ge
    @21
    cB
    fprodge1.b
    ltpnfd
    elicod
    c1
    @3
    wcel
    #
    wph
    @22
    @5
    c1
    c1
    cle
    wbr
    #
    c1
    cpnf
    clt
    wbr
    #
    w3a
    #
    @5
    @23
    @24
    1re
    1le1
    @5
    @24
    1re
    c1
    ltpnf
    ax-mp
    3pm3.2i
    @5
    @1
    @22
    @25
    wb
    1re
    pnfxr
    c1
    cpnf
    c1
    elico2
    mp2an
    mpbir
    a1i
    fprodcllemf
    c1
    cpnf
    @2
    icogelb
    syl3anc
end
