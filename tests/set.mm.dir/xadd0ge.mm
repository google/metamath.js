include "cc0.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "cxr.mm"
include "wcel.mm"
include "wceq.mm"
include "xaddid1.mm"
include "syl.mm"
include "eqcomd.mm"
include "wa.mm"
include "wbr.mm"
include "0xr.mm"
include "a1i.mm"
include "jca.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "xrleid.mm"
include "pnfxr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "xle2add.mm"
include "sylc.mm"
include "eqbrtrd.mm"

theorem xadd0ge
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xadd0ge.a: |- ( ph -> A e. RR* )
  assume xadd0ge.b: |- ( ph -> B e. ( 0 [,] +oo ) )


  assert |- ( ph -> A <_ ( A +e B ) )

  proof
    wph
    cA
    cA
    cc0
    cxad
    co
    #
    cA
    cB
    cxad
    co
    #
    cle
    wph
    @0
    cA
    wph
    cA
    cxr
    wcel
    #
    @0
    cA
    wceq
    xadd0ge.a
    cA
    xaddid1
    syl
    eqcomd
    wph
    @2
    cc0
    cxr
    wcel
    #
    wa
    #
    @2
    cB
    cxr
    wcel
    #
    wa
    #
    wa
    cA
    cA
    cle
    wbr
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    @0
    @1
    cle
    wbr
    wph
    @4
    @6
    wph
    @2
    @3
    xadd0ge.a
    @3
    wph
    0xr
    a1i
    #
    jca
    wph
    @2
    @5
    xadd0ge.a
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cB
    cc0
    cpnf
    iccssxr
    xadd0ge.b
    sseldi
    jca
    jca
    wph
    @7
    @8
    wph
    @2
    @7
    xadd0ge.a
    cA
    xrleid
    syl
    wph
    @3
    cpnf
    cxr
    wcel
    #
    cB
    @10
    wcel
    @8
    @9
    @11
    wph
    pnfxr
    a1i
    xadd0ge.b
    cc0
    cpnf
    cB
    iccgelb
    syl3anc
    jca
    cA
    cc0
    cA
    cB
    xle2add
    sylc
    eqbrtrd
end
