include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "cle.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "lenltd.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "avglt2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "avglt1.mm"
include "wi.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "sylbird.mm"
include "imp.mm"
include "cif.mm"
include "cop.mm"
include "cxp.mm"
include "wceq.mm"
include "ruclem1.mm"
include "simp2d.mm"
include "iffalse.mm"
include "sylan9eq.mm"
include "breqtrrd.mm"
include "ex.mm"
include "con1d.mm"
include "simp3d.mm"
include "iftrue.mm"
include "simpr.mm"
include "eqbrtrd.mm"
include "syld.mm"
include "orrd.mm"

theorem ruclem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let vm: setvar m
  let cF: class F
  let cM: class M
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z
  let cC: class C
  let vn: setvar n
  let vk: setvar k
  let cG: class G
  let cN: class N
  let cS: class S
  assume ruc.1: |- ( ph -> F : NN --> RR )
  assume ruc.2: |- ( ph -> D = ( x e. ( RR X. RR ) , y e. RR |-> [_ ( ( ( 1st ` x ) + ( 2nd ` x ) ) / 2 ) / m ]_ if ( m < y , <. ( 1st ` x ) , m >. , <. ( ( m + ( 2nd ` x ) ) / 2 ) , ( 2nd ` x ) >. ) ) )
  assume ruclem1.3: |- ( ph -> A e. RR )
  assume ruclem1.4: |- ( ph -> B e. RR )
  assume ruclem1.5: |- ( ph -> M e. RR )
  assume ruclem1.6: |- X = ( 1st ` ( <. A , B >. D M ) )
  assume ruclem1.7: |- Y = ( 2nd ` ( <. A , B >. D M ) )
  assume ruclem2.8: |- ( ph -> A < B )

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint M m
  disjoint M x
  disjoint M y
  disjoint m w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint C z
  disjoint m n
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M k
  disjoint M n
  disjoint N k
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint k w
  disjoint k ph
  disjoint n w
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint D w
  disjoint D z
  disjoint S n
  disjoint S z
  assert |- ( ph -> ( M < X \/ Y < M ) )

  proof
    wph
    cM
    cX
    clt
    wbr
    #
    cY
    cM
    clt
    wbr
    #
    wph
    @0
    wn
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cM
    clt
    wbr
    #
    @1
    wph
    @4
    @0
    wph
    @4
    wn
    #
    @0
    wph
    @5
    wa
    cM
    @3
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cX
    clt
    wph
    @5
    cM
    @7
    clt
    wbr
    #
    wph
    @5
    cM
    @3
    cle
    wbr
    #
    @8
    wph
    cM
    @3
    ruclem1.5
    wph
    @2
    wph
    cA
    cB
    ruclem1.3
    ruclem1.4
    readdcld
    rehalfcld
    #
    lenltd
    wph
    @9
    @3
    @7
    clt
    wbr
    #
    @8
    wph
    @3
    cB
    clt
    wbr
    #
    @11
    wph
    cA
    cB
    clt
    wbr
    #
    @12
    ruclem2.8
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    #
    @13
    @12
    wb
    ruclem1.3
    ruclem1.4
    cA
    cB
    avglt2
    syl2anc
    mpbid
    wph
    @3
    cr
    wcel
    #
    @14
    @12
    @11
    wb
    @10
    ruclem1.4
    @3
    cB
    avglt1
    syl2anc
    mpbid
    wph
    cM
    cr
    wcel
    @15
    @7
    cr
    wcel
    @9
    @11
    wa
    @8
    wi
    ruclem1.5
    @10
    wph
    @6
    wph
    @3
    cB
    @10
    ruclem1.4
    readdcld
    rehalfcld
    cM
    @3
    @7
    lelttr
    syl3anc
    mpan2d
    sylbird
    imp
    wph
    @5
    cX
    @4
    cA
    @7
    cif
    #
    @7
    wph
    cA
    cB
    cop
    cM
    cD
    co
    cr
    cr
    cxp
    wcel
    #
    cX
    @16
    wceq
    #
    cY
    @4
    @3
    cB
    cif
    #
    wceq
    #
    wph
    vx
    vy
    cA
    cB
    cD
    vm
    cF
    cM
    cX
    cY
    ruc.1
    ruc.2
    ruclem1.3
    ruclem1.4
    ruclem1.5
    ruclem1.6
    ruclem1.7
    ruclem1
    #
    simp2d
    @4
    cA
    @7
    iffalse
    sylan9eq
    breqtrrd
    ex
    con1d
    wph
    @4
    @1
    wph
    @4
    wa
    cY
    @3
    cM
    clt
    wph
    @4
    cY
    @19
    @3
    wph
    @17
    @18
    @20
    @21
    simp3d
    @4
    @3
    cB
    iftrue
    sylan9eq
    wph
    @4
    simpr
    eqbrtrd
    ex
    syld
    orrd
end
