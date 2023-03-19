include "cfv.mm"
include "c1st.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "c2nd.mm"
include "cr.mm"
include "cxp.mm"
include "wcel.mm"
include "cn0.mm"
include "ruclem6.mm"
include "ffvelrnd.mm"
include "xp1st.mm"
include "syl.mm"
include "ifcld.mm"
include "xp2nd.mm"
include "cuz.mm"
include "nn0red.mm"
include "max1.mm"
include "syl2anc.mm"
include "cz.mm"
include "wb.mm"
include "nn0zd.mm"
include "eluz.mm"
include "mpbird.mm"
include "ruclem9.mm"
include "simpld.mm"
include "clt.mm"
include "ruclem8.mm"
include "mpdan.mm"
include "max2.mm"
include "simprd.mm"
include "ltletrd.mm"
include "lelttrd.mm"

theorem ruclem10
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vn: setvar n
  let vk: setvar k
  let cS: class S
  assume ruc.1: |- ( ph -> F : NN --> RR )
  assume ruc.2: |- ( ph -> D = ( x e. ( RR X. RR ) , y e. RR |-> [_ ( ( ( 1st ` x ) + ( 2nd ` x ) ) / 2 ) / m ]_ if ( m < y , <. ( 1st ` x ) , m >. , <. ( ( m + ( 2nd ` x ) ) / 2 ) , ( 2nd ` x ) >. ) ) )
  assume ruc.4: |- C = ( { <. 0 , <. 0 , 1 >. >. } u. F )
  assume ruc.5: |- G = seq 0 ( D , C )
  assume ruclem10.6: |- ( ph -> M e. NN0 )
  assume ruclem10.7: |- ( ph -> N e. NN0 )

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint M m
  disjoint M x
  disjoint M y
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint m w
  disjoint w x
  disjoint w y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
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
  disjoint G n
  disjoint G z
  disjoint M k
  disjoint M n
  disjoint N k
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
  assert |- ( ph -> ( 1st ` ( G ` M ) ) < ( 2nd ` ( G ` N ) ) )

  proof
    wph
    cM
    cG
    cfv
    #
    c1st
    cfv
    #
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cif
    #
    cG
    cfv
    #
    c1st
    cfv
    #
    cN
    cG
    cfv
    #
    c2nd
    cfv
    #
    wph
    @0
    cr
    cr
    cxp
    #
    wcel
    @1
    cr
    wcel
    wph
    cn0
    @8
    cM
    cG
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem6
    #
    ruclem10.6
    ffvelrnd
    @0
    cr
    cr
    xp1st
    syl
    wph
    @4
    @8
    wcel
    #
    @5
    cr
    wcel
    wph
    cn0
    @8
    @3
    cG
    @9
    wph
    @2
    cN
    cM
    cn0
    ruclem10.7
    ruclem10.6
    ifcld
    #
    ffvelrnd
    #
    @4
    cr
    cr
    xp1st
    syl
    #
    wph
    @6
    @8
    wcel
    @7
    cr
    wcel
    wph
    cn0
    @8
    cN
    cG
    @9
    ruclem10.7
    ffvelrnd
    @6
    cr
    cr
    xp2nd
    syl
    #
    wph
    @1
    @5
    cle
    wbr
    @4
    c2nd
    cfv
    #
    @0
    c2nd
    cfv
    cle
    wbr
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    cM
    @3
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem10.6
    wph
    @3
    cM
    cuz
    cfv
    wcel
    #
    cM
    @3
    cle
    wbr
    #
    wph
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @17
    wph
    cM
    ruclem10.6
    nn0red
    #
    wph
    cN
    ruclem10.7
    nn0red
    #
    cM
    cN
    max1
    syl2anc
    wph
    cM
    cz
    wcel
    @3
    cz
    wcel
    #
    @16
    @17
    wb
    wph
    cM
    ruclem10.6
    nn0zd
    wph
    @3
    @11
    nn0zd
    #
    cM
    @3
    eluz
    syl2anc
    mpbird
    ruclem9
    simpld
    wph
    @5
    @15
    @7
    @13
    wph
    @10
    @15
    cr
    wcel
    @12
    @4
    cr
    cr
    xp2nd
    syl
    @14
    wph
    @3
    cn0
    wcel
    @5
    @15
    clt
    wbr
    @11
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    @3
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem8
    mpdan
    wph
    @6
    c1st
    cfv
    @5
    cle
    wbr
    @15
    @7
    cle
    wbr
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    cN
    @3
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem10.7
    wph
    @3
    cN
    cuz
    cfv
    wcel
    #
    cN
    @3
    cle
    wbr
    #
    wph
    @18
    @19
    @25
    @20
    @21
    cM
    cN
    max2
    syl2anc
    wph
    cN
    cz
    wcel
    @22
    @24
    @25
    wb
    wph
    cN
    ruclem10.7
    nn0zd
    @23
    cN
    @3
    eluz
    syl2anc
    mpbird
    ruclem9
    simprd
    ltletrd
    lelttrd
end
