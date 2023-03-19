include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "co.mm"
include "cicc.mm"
include "cfv.mm"
include "covol.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "cop.mm"
include "dyadval.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cn.mm"
include "zre.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "mpan.mm"
include "nndivre.mm"
include "syl2an.mm"
include "peano2re.mm"
include "syl.mm"
include "adantr.mm"
include "lep1d.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "adantl.mm"
include "nnred.mm"
include "nngt0d.mm"
include "lediv1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ovolicc.mm"
include "syl3anc.mm"
include "recnd.mm"
include "nnne0d.mm"
include "divsubdird.mm"
include "cc.mm"
include "ax-1cn.mm"
include "pncan2.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "3eqtrd.mm"

theorem dyadovol
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z
  let wph: wff ph
  let vi: setvar i
  let vr: setvar r
  let cD: class D
  let cG: class G
  assume dyadmbl.1: |- F = ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint c d
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint f x
  disjoint f y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint C x
  disjoint C y
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b w
  disjoint b z
  disjoint b ph
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint f ph
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint m z
  disjoint m ph
  disjoint n t
  disjoint n w
  disjoint n z
  disjoint n ph
  disjoint t w
  disjoint t z
  disjoint ph t
  disjoint w z
  disjoint ph w
  disjoint ph z
  disjoint a i
  disjoint a r
  disjoint A a
  disjoint b i
  disjoint b r
  disjoint A b
  disjoint c i
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint d i
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d w
  disjoint d z
  disjoint A d
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i t
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint D x
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G t
  disjoint G z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F m
  disjoint F n
  disjoint F r
  disjoint F w
  disjoint F z
  assert |- ( ( A e. ZZ /\ B e. NN0 ) -> ( vol* ` ( [,] ` ( A F B ) ) ) = ( 1 / ( 2 ^ B ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    #
    cA
    cB
    cF
    co
    #
    cicc
    cfv
    #
    covol
    cfv
    cA
    c2
    cB
    cexp
    co
    #
    cdiv
    co
    #
    cA
    c1
    caddc
    co
    #
    @5
    cdiv
    co
    #
    cicc
    co
    #
    covol
    cfv
    #
    @8
    @6
    cmin
    co
    #
    c1
    @5
    cdiv
    co
    #
    @2
    @4
    @9
    covol
    @2
    @4
    @6
    @8
    cop
    #
    cicc
    cfv
    @9
    @2
    @3
    @13
    cicc
    vx
    vy
    cA
    cB
    cF
    dyadmbl.1
    dyadval
    fveq2d
    @6
    @8
    cicc
    df-ov
    syl6eqr
    fveq2d
    @2
    @6
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @6
    @8
    cle
    wbr
    #
    @10
    @11
    wceq
    @0
    cA
    cr
    wcel
    #
    @5
    cn
    wcel
    #
    @14
    @1
    cA
    zre
    #
    c2
    cn
    wcel
    @1
    @18
    2nn
    c2
    cB
    nnexpcl
    mpan
    #
    cA
    @5
    nndivre
    syl2an
    @0
    @7
    cr
    wcel
    #
    @18
    @15
    @1
    @0
    @17
    @21
    @19
    cA
    peano2re
    #
    syl
    @20
    @7
    @5
    nndivre
    syl2an
    @2
    cA
    @7
    cle
    wbr
    #
    @16
    @2
    cA
    @0
    @17
    @1
    @19
    adantr
    #
    lep1d
    @2
    @17
    @21
    @5
    cr
    wcel
    cc0
    @5
    clt
    wbr
    @23
    @16
    wb
    @24
    @2
    @17
    @21
    @24
    @22
    syl
    #
    @2
    @5
    @1
    @18
    @0
    @20
    adantl
    #
    nnred
    #
    @2
    @5
    @26
    nngt0d
    cA
    @7
    @5
    lediv1
    syl112anc
    mpbid
    @6
    @8
    ovolicc
    syl3anc
    @2
    @7
    cA
    cmin
    co
    #
    @5
    cdiv
    co
    @11
    @12
    @2
    @7
    cA
    @5
    @2
    @7
    @25
    recnd
    @2
    cA
    @24
    recnd
    #
    @2
    @5
    @27
    recnd
    @2
    @5
    @26
    nnne0d
    divsubdird
    @2
    @28
    c1
    @5
    cdiv
    @2
    cA
    cc
    wcel
    c1
    cc
    wcel
    @28
    c1
    wceq
    @29
    ax-1cn
    cA
    c1
    pncan2
    sylancl
    oveq1d
    eqtr3d
    3eqtrd
end
