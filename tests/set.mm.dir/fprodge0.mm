include "cprod.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cc.mm"
include "wss.mm"
include "cr.mm"
include "cv.mm"
include "elrege0.mm"
include "simplbi.mm"
include "ssriv.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "a1i.mm"
include "wa.mm"
include "cmul.mm"
include "ge0mulcl.mm"
include "adantl.mm"
include "sylanbrc.mm"
include "c1.mm"
include "clt.mm"
include "w3a.mm"
include "1re.mm"
include "0le1.mm"
include "ltpnf.mm"
include "ax-mp.mm"
include "3pm3.2i.mm"
include "cxr.mm"
include "wb.mm"
include "0e0icopnf.mm"
include "sselii.mm"
include "pnfxr.mm"
include "elico2.mm"
include "mp2an.mm"
include "mpbir.mm"
include "fprodcllemf.mm"
include "0xr.mm"
include "id.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "syl.mm"

theorem fprodge0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fprodge0.kph: |- F/ k ph
  assume fprodge0.a: |- ( ph -> A e. Fin )
  assume fprodge0.b: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume fprodge0.0leb: |- ( ( ph /\ k e. A ) -> 0 <_ B )

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
  assert |- ( ph -> 0 <_ prod_ k e. A B )

  proof
    wph
    cA
    cB
    vk
    cprod
    #
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    cc0
    @0
    cle
    wbr
    #
    wph
    vx
    vy
    cA
    cB
    @1
    vk
    fprodge0.kph
    @1
    cc
    wss
    wph
    @1
    cr
    cc
    vx
    @1
    cr
    vx
    cv
    #
    @1
    wcel
    #
    @4
    cr
    wcel
    cc0
    @4
    cle
    wbr
    @4
    elrege0
    simplbi
    ssriv
    #
    ax-resscn
    sstri
    a1i
    @5
    vy
    cv
    #
    @1
    wcel
    wa
    @4
    @7
    cmul
    co
    @1
    wcel
    wph
    @4
    @7
    ge0mulcl
    adantl
    fprodge0.a
    wph
    vk
    cv
    cA
    wcel
    wa
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    cB
    @1
    wcel
    fprodge0.b
    fprodge0.0leb
    cB
    elrege0
    sylanbrc
    c1
    @1
    wcel
    #
    wph
    @8
    c1
    cr
    wcel
    #
    cc0
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
    @9
    @10
    @11
    1re
    0le1
    @9
    @11
    1re
    c1
    ltpnf
    ax-mp
    3pm3.2i
    cc0
    cr
    wcel
    cpnf
    cxr
    wcel
    #
    @8
    @12
    wb
    @1
    cr
    cc0
    @6
    0e0icopnf
    sselii
    pnfxr
    cc0
    cpnf
    c1
    elico2
    mp2an
    mpbir
    a1i
    fprodcllemf
    @2
    cc0
    cxr
    wcel
    #
    @13
    @2
    @3
    @14
    @2
    0xr
    a1i
    @13
    @2
    pnfxr
    a1i
    @2
    id
    cc0
    cpnf
    @0
    icogelb
    syl3anc
    syl
end
