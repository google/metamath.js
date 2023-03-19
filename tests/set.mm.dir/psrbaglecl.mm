include "wcel.mm"
include "cn0.mm"
include "wf.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "simpr2.mm"
include "wss.mm"
include "simpr1.mm"
include "wb.mm"
include "psrbag.mm"
include "adantr.mm"
include "mpbid.mm"
include "simprd.mm"
include "psrbaglesupp.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem psrbaglecl
  let cD: class D
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let cS: class S
  let cB: class B
  let cX: class X
  let cY: class Y
  assume psrbag.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }

  disjoint F f
  disjoint G f
  disjoint I f
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint V m
  disjoint V n
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint I m
  disjoint I n
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S z
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint D j
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint X f
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y k
  disjoint Y m
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( I e. V /\ ( F e. D /\ G : I --> NN0 /\ G oR <_ F ) ) -> G e. D )

  proof
    cI
    cV
    wcel
    #
    cF
    cD
    wcel
    #
    cI
    cn0
    cG
    wf
    #
    cG
    cF
    cle
    cofr
    wbr
    #
    w3a
    #
    wa
    #
    cG
    cD
    wcel
    #
    @2
    cG
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    @0
    @1
    @2
    @3
    simpr2
    @5
    cF
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    @7
    @9
    wss
    @8
    @5
    cI
    cn0
    cF
    wf
    #
    @10
    @5
    @1
    @11
    @10
    wa
    #
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @12
    wb
    @4
    cD
    vf
    cF
    cI
    cV
    psrbag.d
    psrbag
    adantr
    mpbid
    simprd
    cD
    vf
    cF
    cG
    cI
    cV
    psrbag.d
    psrbaglesupp
    @9
    @7
    ssfi
    syl2anc
    @0
    @6
    @2
    @8
    wa
    wb
    @4
    cD
    vf
    cG
    cI
    cV
    psrbag.d
    psrbag
    adantr
    mpbir2and
end
