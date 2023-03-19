include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cif.mm"
include "leidd.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "avglt1.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "avglt2.mm"
include "lttrd.mm"
include "ltled.mm"
include "breq2.mm"
include "ifboth.mm"
include "cop.mm"
include "cxp.mm"
include "wceq.mm"
include "ruclem1.mm"
include "simp2d.mm"
include "breqtrrd.mm"
include "iftrue.mm"
include "breq12d.mm"
include "syl5ibrcom.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61d.mm"
include "simp3d.mm"
include "3brtr4d.mm"
include "breq1.mm"
include "eqbrtrd.mm"
include "3jca.mm"

theorem ruclem2
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
  assert |- ( ph -> ( A <_ X /\ X < Y /\ Y <_ B ) )

  proof
    wph
    cA
    cX
    cle
    wbr
    cX
    cY
    clt
    wbr
    cY
    cB
    cle
    wbr
    wph
    cA
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
    cA
    @1
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cif
    #
    cX
    cle
    wph
    cA
    cA
    cle
    wbr
    #
    cA
    @4
    cle
    wbr
    #
    cA
    @5
    cle
    wbr
    #
    wph
    cA
    ruclem1.3
    leidd
    wph
    cA
    @4
    ruclem1.3
    wph
    @3
    wph
    @1
    cB
    wph
    @0
    wph
    cA
    cB
    ruclem1.3
    ruclem1.4
    readdcld
    rehalfcld
    #
    ruclem1.4
    readdcld
    rehalfcld
    #
    wph
    cA
    @1
    @4
    ruclem1.3
    @9
    @10
    wph
    cA
    cB
    clt
    wbr
    #
    cA
    @1
    clt
    wbr
    #
    ruclem2.8
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @11
    @12
    wb
    ruclem1.3
    ruclem1.4
    cA
    cB
    avglt1
    syl2anc
    mpbid
    #
    wph
    @1
    cB
    clt
    wbr
    #
    @1
    @4
    clt
    wbr
    #
    wph
    @11
    @16
    ruclem2.8
    wph
    @13
    @14
    @11
    @16
    wb
    ruclem1.3
    ruclem1.4
    cA
    cB
    avglt2
    syl2anc
    mpbid
    #
    wph
    @1
    cr
    wcel
    #
    @14
    @16
    @17
    wb
    @9
    ruclem1.4
    @1
    cB
    avglt1
    syl2anc
    mpbid
    lttrd
    ltled
    @2
    @6
    @7
    @8
    cA
    @4
    cA
    @5
    cA
    cle
    breq2
    @4
    @5
    cA
    cle
    breq2
    ifboth
    syl2anc
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
    @5
    wceq
    #
    cY
    @2
    @1
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
    #
    breqtrrd
    wph
    @5
    @22
    cX
    cY
    clt
    wph
    @2
    @5
    @22
    clt
    wbr
    #
    wph
    @26
    @2
    @12
    @15
    @2
    @5
    cA
    @22
    @1
    clt
    @2
    cA
    @4
    iftrue
    @2
    @1
    cB
    iftrue
    breq12d
    syl5ibrcom
    wph
    @26
    @2
    wn
    #
    @4
    cB
    clt
    wbr
    #
    wph
    @16
    @28
    @18
    wph
    @19
    @14
    @16
    @28
    wb
    @9
    ruclem1.4
    @1
    cB
    avglt2
    syl2anc
    mpbid
    @27
    @5
    @4
    @22
    cB
    clt
    @2
    cA
    @4
    iffalse
    @2
    @1
    cB
    iffalse
    breq12d
    syl5ibrcom
    pm2.61d
    @25
    wph
    @20
    @21
    @23
    @24
    simp3d
    #
    3brtr4d
    wph
    cY
    @22
    cB
    cle
    @29
    wph
    @1
    cB
    cle
    wbr
    #
    cB
    cB
    cle
    wbr
    #
    @22
    cB
    cle
    wbr
    #
    wph
    @1
    cB
    @9
    ruclem1.4
    @18
    ltled
    wph
    cB
    ruclem1.4
    leidd
    @2
    @30
    @31
    @32
    @1
    cB
    @1
    @22
    cB
    cle
    breq1
    cB
    @22
    cB
    cle
    breq1
    ifboth
    syl2anc
    eqbrtrd
    3jca
end
