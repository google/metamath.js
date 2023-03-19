include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "cmo.mm"
include "clt.mm"
include "cico.mm"
include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "wss.mm"
include "modcld.mm"
include "resubcld.mm"
include "rexrd.mm"
include "icossre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "rpred.mm"
include "rerpdivcld.mm"
include "flcld.mm"
include "zred.mm"
include "remulcld.mm"
include "wbr.mm"
include "icoltub.mm"
include "syl3anc.mm"
include "ltsub1dd.mm"
include "cicc.mm"
include "icossicc.mm"
include "sseldi.mm"
include "lefldiveq.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "breqtrd.mm"
include "crp.mm"
include "wceq.mm"
include "modval.mm"
include "3brtr4d.mm"

theorem ltmod
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltmod.a: |- ( ph -> A e. RR )
  assume ltmod.b: |- ( ph -> B e. RR+ )
  assume ltmod.c: |- ( ph -> C e. ( ( A - ( A mod B ) ) [,) A ) )


  assert |- ( ph -> ( C mod B ) < ( A mod B ) )

  proof
    wph
    cC
    cB
    cC
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cA
    cB
    cA
    cB
    cdiv
    co
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cC
    cB
    cmo
    co
    #
    cA
    cB
    cmo
    co
    #
    clt
    wph
    @3
    cA
    @2
    cmin
    co
    @6
    clt
    wph
    cC
    cA
    @2
    wph
    cA
    @8
    cmin
    co
    #
    cA
    cico
    co
    #
    cr
    cC
    wph
    @9
    cr
    wcel
    cA
    cxr
    wcel
    #
    @10
    cr
    wss
    wph
    cA
    @8
    ltmod.a
    wph
    cA
    cB
    ltmod.a
    ltmod.b
    modcld
    resubcld
    #
    wph
    cA
    ltmod.a
    rexrd
    #
    @9
    cA
    icossre
    syl2anc
    ltmod.c
    sseldd
    #
    ltmod.a
    wph
    cB
    @1
    wph
    cB
    ltmod.b
    rpred
    wph
    @1
    wph
    @0
    wph
    cC
    cB
    @14
    ltmod.b
    rerpdivcld
    flcld
    zred
    remulcld
    wph
    @9
    cxr
    wcel
    @11
    cC
    @10
    wcel
    cC
    cA
    clt
    wbr
    wph
    @9
    @12
    rexrd
    @13
    ltmod.c
    @9
    cA
    cC
    icoltub
    syl3anc
    ltsub1dd
    wph
    @2
    @5
    cA
    cmin
    wph
    @1
    @4
    cB
    cmul
    wph
    @4
    @1
    wph
    cA
    cB
    cC
    ltmod.a
    ltmod.b
    wph
    @10
    @9
    cA
    cicc
    co
    cC
    @9
    cA
    icossicc
    ltmod.c
    sseldi
    lefldiveq
    eqcomd
    oveq2d
    oveq2d
    breqtrd
    wph
    cC
    cr
    wcel
    cB
    crp
    wcel
    #
    @7
    @3
    wceq
    @14
    ltmod.b
    cC
    cB
    modval
    syl2anc
    wph
    cA
    cr
    wcel
    @15
    @8
    @6
    wceq
    ltmod.a
    ltmod.b
    cA
    cB
    modval
    syl2anc
    3brtr4d
end
