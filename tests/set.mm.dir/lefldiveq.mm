include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cmo.mm"
include "cmin.mm"
include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "crp.mm"
include "moddiffl.mm"
include "syl2anc.mm"
include "rerpdivcld.mm"
include "flcld.mm"
include "eqeltrd.mm"
include "flid.mm"
include "syl.mm"
include "eqtr2d.mm"
include "modcld.mm"
include "resubcld.mm"
include "cicc.mm"
include "wss.mm"
include "iccssre.mm"
include "sseldd.mm"
include "cxr.mm"
include "rexrd.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "lediv1dd.mm"
include "flwordi.mm"
include "eqbrtrd.mm"
include "iccleub.mm"
include "reflcl.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem lefldiveq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume lefldiveq.a: |- ( ph -> A e. RR )
  assume lefldiveq.b: |- ( ph -> B e. RR+ )
  assume lefldiveq.c: |- ( ph -> C e. ( ( A - ( A mod B ) ) [,] A ) )


  assert |- ( ph -> ( |_ ` ( A / B ) ) = ( |_ ` ( C / B ) ) )

  proof
    wph
    cA
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    cC
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    wceq
    @1
    @3
    cle
    wbr
    @3
    @1
    cle
    wbr
    #
    wph
    @1
    cA
    cA
    cB
    cmo
    co
    #
    cmin
    co
    #
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    @3
    cle
    wph
    @8
    @7
    @1
    wph
    @7
    cz
    wcel
    @8
    @7
    wceq
    wph
    @7
    @1
    cz
    wph
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    @7
    @1
    wceq
    lefldiveq.a
    lefldiveq.b
    cA
    cB
    moddiffl
    syl2anc
    #
    wph
    @0
    wph
    cA
    cB
    lefldiveq.a
    lefldiveq.b
    rerpdivcld
    #
    flcld
    eqeltrd
    @7
    flid
    syl
    @10
    eqtr2d
    wph
    @7
    cr
    wcel
    @2
    cr
    wcel
    #
    @7
    @2
    cle
    wbr
    @8
    @3
    cle
    wbr
    wph
    @6
    cB
    wph
    cA
    @5
    lefldiveq.a
    wph
    cA
    cB
    lefldiveq.a
    lefldiveq.b
    modcld
    resubcld
    #
    lefldiveq.b
    rerpdivcld
    wph
    cC
    cB
    wph
    @6
    cA
    cicc
    co
    #
    cr
    cC
    wph
    @6
    cr
    wcel
    @9
    @14
    cr
    wss
    @13
    lefldiveq.a
    @6
    cA
    iccssre
    syl2anc
    lefldiveq.c
    sseldd
    #
    lefldiveq.b
    rerpdivcld
    #
    wph
    @6
    cC
    cB
    @13
    @15
    lefldiveq.b
    wph
    @6
    cxr
    wcel
    #
    cA
    cxr
    wcel
    #
    cC
    @14
    wcel
    #
    @6
    cC
    cle
    wbr
    wph
    @6
    @13
    rexrd
    #
    wph
    cA
    lefldiveq.a
    rexrd
    #
    lefldiveq.c
    @6
    cA
    cC
    iccgelb
    syl3anc
    lediv1dd
    @7
    @2
    flwordi
    syl3anc
    eqbrtrd
    wph
    @12
    @0
    cr
    wcel
    #
    @2
    @0
    cle
    wbr
    @4
    @16
    @11
    wph
    cC
    cA
    cB
    @15
    lefldiveq.a
    lefldiveq.b
    wph
    @17
    @18
    @19
    cC
    cA
    cle
    wbr
    @20
    @21
    lefldiveq.c
    @6
    cA
    cC
    iccleub
    syl3anc
    lediv1dd
    @2
    @0
    flwordi
    syl3anc
    wph
    @1
    @3
    wph
    @22
    @1
    cr
    wcel
    @11
    @0
    reflcl
    syl
    wph
    @12
    @3
    cr
    wcel
    @16
    @2
    reflcl
    syl
    letri3d
    mpbir2and
end
