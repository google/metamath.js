include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cop.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wcel.mm"
include "cn0.mm"
include "wral.mm"
include "cz.mm"
include "wf.mm"
include "wa.mm"
include "wbr.mm"
include "zre.mm"
include "adantr.mm"
include "lep1d.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "peano2re.mm"
include "syl.mm"
include "cn.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "mpan.mm"
include "adantl.mm"
include "nnred.mm"
include "nngt0d.mm"
include "lediv1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "df-br.mm"
include "sylib.mm"
include "nndivre.mm"
include "syl2an.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "elind.mm"
include "rgen2.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem dyadf
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z
  let wph: wff ph
  let vi: setvar i
  let vr: setvar r
  let cA: class A
  let cD: class D
  let cG: class G
  assume dyadmbl.1: |- F = ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. )

  disjoint x y
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
  disjoint B x
  disjoint B y
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
  disjoint A x
  disjoint y z
  disjoint A y
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
  assert |- F : ( ZZ X. NN0 ) --> ( <_ i^i ( RR X. RR ) )

  proof
    vx
    cv
    #
    c2
    vy
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @0
    c1
    caddc
    co
    #
    @2
    cdiv
    co
    #
    cop
    #
    cle
    cr
    cr
    cxp
    #
    cin
    #
    wcel
    #
    vy
    cn0
    wral
    vx
    cz
    wral
    cz
    cn0
    cxp
    @8
    cF
    wf
    @9
    vx
    vy
    cz
    cn0
    @0
    cz
    wcel
    #
    @1
    cn0
    wcel
    #
    wa
    #
    cle
    @7
    @6
    @12
    @3
    @5
    cle
    wbr
    #
    @6
    cle
    wcel
    @12
    @0
    @4
    cle
    wbr
    #
    @13
    @12
    @0
    @10
    @0
    cr
    wcel
    #
    @11
    @0
    zre
    #
    adantr
    #
    lep1d
    @12
    @15
    @4
    cr
    wcel
    #
    @2
    cr
    wcel
    cc0
    @2
    clt
    wbr
    @14
    @13
    wb
    @17
    @12
    @15
    @18
    @17
    @0
    peano2re
    #
    syl
    @12
    @2
    @11
    @2
    cn
    wcel
    #
    @10
    c2
    cn
    wcel
    @11
    @20
    2nn
    c2
    @1
    nnexpcl
    mpan
    #
    adantl
    #
    nnred
    @12
    @2
    @22
    nngt0d
    @0
    @4
    @2
    lediv1
    syl112anc
    mpbid
    @3
    @5
    cle
    df-br
    sylib
    @12
    @3
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @6
    @7
    wcel
    @10
    @15
    @20
    @23
    @11
    @16
    @21
    @0
    @2
    nndivre
    syl2an
    @10
    @18
    @20
    @24
    @11
    @10
    @15
    @18
    @16
    @19
    syl
    @21
    @4
    @2
    nndivre
    syl2an
    @3
    @5
    cr
    cr
    opelxpi
    syl2anc
    elind
    rgen2
    vx
    vy
    cz
    cn0
    @6
    @8
    cF
    dyadmbl.1
    fmpt2
    mpbi
end
