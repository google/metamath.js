include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "c1.mm"
include "cmul.mm"
include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "nncnd.mm"
include "subcld.mm"
include "npcand.mm"
include "subsub4d.mm"
include "addcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "cuz.mm"
include "cfv.mm"
include "cfz.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cmap.mm"
include "wf.mm"
include "wceq.mm"
include "vdwlem4.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "cvdwa.mm"
include "cun.mm"
include "ssun2.mm"
include "c2.mm"
include "uz2m1nn.mm"
include "nnaddcld.mm"
include "vdwapid1.mm"
include "syl3anc.mm"
include "sseldi.mm"
include "cc.mm"
include "eluz2nn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "nnm1nn0.mm"
include "vdwapun.mm"
include "eqtr3d.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "elfzuz3.mm"
include "uznn0sub.mm"
include "eqeltrd.mm"
include "nn0nnaddcl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "nn0mulcld.mm"
include "nnnn0addcl.mm"
include "syl5eqel.mm"

theorem vdwlem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z
  let va: setvar a
  let vd: setvar d
  assume vdwlem3.v: |- ( ph -> V e. NN )
  assume vdwlem3.w: |- ( ph -> W e. NN )
  assume vdwlem4.r: |- ( ph -> R e. Fin )
  assume vdwlem4.h: |- ( ph -> H : ( 1 ... ( W x. ( 2 x. V ) ) ) --> R )
  assume vdwlem4.f: |- F = ( x e. ( 1 ... V ) |-> ( y e. ( 1 ... W ) |-> ( H ` ( y + ( W x. ( ( x - 1 ) + V ) ) ) ) ) )
  assume vdwlem7.m: |- ( ph -> M e. NN )
  assume vdwlem7.g: |- ( ph -> G : ( 1 ... W ) --> R )
  assume vdwlem7.k: |- ( ph -> K e. ( ZZ>= ` 2 ) )
  assume vdwlem7.a: |- ( ph -> A e. NN )
  assume vdwlem7.d: |- ( ph -> D e. NN )
  assume vdwlem7.s: |- ( ph -> ( A ( AP ` K ) D ) C_ ( `' F " { G } ) )
  assume vdwlem6.b: |- ( ph -> B e. NN )
  assume vdwlem6.e: |- ( ph -> E : ( 1 ... M ) --> NN )
  assume vdwlem6.s: |- ( ph -> A. i e. ( 1 ... M ) ( ( B + ( E ` i ) ) ( AP ` K ) ( E ` i ) ) C_ ( `' G " { ( G ` ( B + ( E ` i ) ) ) } ) )
  assume vdwlem6.j: |- J = ( i e. ( 1 ... M ) |-> ( G ` ( B + ( E ` i ) ) ) )
  assume vdwlem6.r: |- ( ph -> ( # ` ran J ) = M )
  assume vdwlem6.t: |- T = ( B + ( W x. ( ( A + ( V - D ) ) - 1 ) ) )
  assume vdwlem6.p: |- P = ( j e. ( 1 ... ( M + 1 ) ) |-> ( if ( j = ( M + 1 ) , 0 , ( E ` j ) ) + ( W x. D ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint i j
  disjoint i x
  disjoint i y
  disjoint G i
  disjoint j x
  disjoint j y
  disjoint G j
  disjoint G x
  disjoint G y
  disjoint K i
  disjoint K j
  disjoint K x
  disjoint K y
  disjoint J i
  disjoint J j
  disjoint J x
  disjoint P i
  disjoint P x
  disjoint i ph
  disjoint j ph
  disjoint ph x
  disjoint ph y
  disjoint R i
  disjoint R x
  disjoint R y
  disjoint B i
  disjoint B j
  disjoint B x
  disjoint B y
  disjoint H i
  disjoint H x
  disjoint H y
  disjoint M i
  disjoint M j
  disjoint M x
  disjoint M y
  disjoint D j
  disjoint D x
  disjoint D y
  disjoint E i
  disjoint E j
  disjoint E x
  disjoint E y
  disjoint W i
  disjoint W j
  disjoint W x
  disjoint W y
  disjoint T i
  disjoint T x
  disjoint V x
  disjoint V y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint a d
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint G a
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint G d
  disjoint i k
  disjoint i m
  disjoint i z
  disjoint j k
  disjoint j m
  disjoint j z
  disjoint G k
  disjoint G m
  disjoint G z
  disjoint a n
  disjoint K a
  disjoint d n
  disjoint K d
  disjoint i n
  disjoint j n
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K z
  disjoint J m
  disjoint P d
  disjoint a ph
  disjoint d ph
  disjoint k ph
  disjoint m ph
  disjoint ph z
  disjoint R k
  disjoint B m
  disjoint B n
  disjoint B z
  disjoint H a
  disjoint H d
  disjoint H k
  disjoint H m
  disjoint H z
  disjoint M a
  disjoint M d
  disjoint M k
  disjoint M m
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D z
  disjoint E m
  disjoint E n
  disjoint W k
  disjoint W m
  disjoint W z
  disjoint T a
  disjoint T d
  disjoint V k
  disjoint V m
  disjoint V z
  assert |- ( ph -> T e. NN )

  proof
    wph
    cT
    cB
    cW
    cA
    cV
    cD
    cmin
    co
    #
    caddc
    co
    #
    c1
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cn
    vdwlem6.t
    wph
    cB
    cn
    wcel
    @3
    cn0
    wcel
    @4
    cn
    wcel
    vdwlem6.b
    wph
    cW
    @2
    wph
    cW
    vdwlem3.w
    nnnn0d
    wph
    @1
    cn
    wcel
    @2
    cn0
    wcel
    wph
    cA
    @0
    vdwlem7.a
    wph
    @0
    cA
    cmin
    co
    #
    cA
    caddc
    co
    #
    @0
    cn
    wph
    @0
    cA
    wph
    cV
    cD
    wph
    cV
    vdwlem3.v
    nncnd
    #
    wph
    cD
    vdwlem7.d
    nncnd
    #
    subcld
    wph
    cA
    vdwlem7.a
    nncnd
    #
    npcand
    wph
    @5
    cn0
    wcel
    cA
    cn
    wcel
    #
    @6
    cn
    wcel
    wph
    @5
    cV
    cA
    cD
    caddc
    co
    #
    cmin
    co
    #
    cn0
    wph
    @5
    cV
    cD
    cA
    caddc
    co
    #
    cmin
    co
    @12
    wph
    cV
    cD
    cA
    @7
    @8
    @9
    subsub4d
    wph
    @13
    @11
    cV
    cmin
    wph
    cD
    cA
    @8
    @9
    addcomd
    oveq2d
    eqtrd
    wph
    cV
    @11
    cuz
    cfv
    wcel
    #
    @12
    cn0
    wcel
    wph
    @11
    c1
    cV
    cfz
    co
    #
    wcel
    @14
    wph
    cF
    ccnv
    cG
    csn
    #
    cima
    #
    @15
    @11
    wph
    cF
    cdm
    #
    @17
    @15
    cF
    @16
    cnvimass
    wph
    @15
    cR
    c1
    cW
    cfz
    co
    cmap
    co
    #
    cF
    wf
    @18
    @15
    wceq
    wph
    vx
    vy
    cR
    cF
    cH
    cV
    cW
    vdwlem3.v
    vdwlem3.w
    vdwlem4.r
    vdwlem4.h
    vdwlem4.f
    vdwlem4
    @15
    @19
    cF
    fdm
    syl
    syl5sseq
    wph
    cA
    cD
    cK
    cvdwa
    cfv
    #
    co
    #
    @17
    @11
    vdwlem7.s
    wph
    @11
    cA
    csn
    #
    @11
    cD
    cK
    c1
    cmin
    co
    #
    cvdwa
    cfv
    co
    #
    cun
    #
    @21
    wph
    @24
    @25
    @11
    @24
    @22
    ssun2
    wph
    @23
    cn
    wcel
    #
    @11
    cn
    wcel
    cD
    cn
    wcel
    #
    @11
    @24
    wcel
    wph
    cK
    c2
    cuz
    cfv
    wcel
    #
    @26
    vdwlem7.k
    cK
    uz2m1nn
    syl
    wph
    cA
    cD
    vdwlem7.a
    vdwlem7.d
    nnaddcld
    vdwlem7.d
    @11
    cD
    @23
    vdwapid1
    syl3anc
    sseldi
    wph
    cA
    cD
    @23
    c1
    caddc
    co
    #
    cvdwa
    cfv
    #
    co
    #
    @21
    @25
    wph
    @30
    @20
    cA
    cD
    wph
    @29
    cK
    cvdwa
    wph
    cK
    cc
    wcel
    c1
    cc
    wcel
    @29
    cK
    wceq
    wph
    cK
    wph
    @28
    cK
    cn
    wcel
    #
    vdwlem7.k
    cK
    eluz2nn
    syl
    #
    nncnd
    ax-1cn
    cK
    c1
    npcan
    sylancl
    fveq2d
    oveqd
    wph
    @23
    cn0
    wcel
    #
    @10
    @27
    @31
    @25
    wceq
    wph
    @32
    @34
    @33
    cK
    nnm1nn0
    syl
    vdwlem7.a
    vdwlem7.d
    cA
    cD
    @23
    vdwapun
    syl3anc
    eqtr3d
    eleqtrrd
    sseldd
    sseldd
    @11
    c1
    cV
    elfzuz3
    syl
    @11
    cV
    uznn0sub
    syl
    eqeltrd
    vdwlem7.a
    @5
    cA
    nn0nnaddcl
    syl2anc
    eqeltrrd
    nnaddcld
    @1
    nnm1nn0
    syl
    nn0mulcld
    cB
    @3
    nnnn0addcl
    syl2anc
    syl5eqel
end
