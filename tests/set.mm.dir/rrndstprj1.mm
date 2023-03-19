include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "crrn.mm"
include "cle.mm"
include "wbr.mm"
include "simpll.mm"
include "cr.mm"
include "cmap.mm"
include "wf.mm"
include "simprl.mm"
include "syl6eleq.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "simprr.mm"
include "resubcld.mm"
include "resqcld.mm"
include "sqge0d.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "simplr.mm"
include "fsumge1.mm"
include "ffvelrnd.mm"
include "absresq.mm"
include "cc0.mm"
include "fsumrecl.mm"
include "fsumge0.mm"
include "resqrtth.mm"
include "syl2anc.mm"
include "3brtr4d.mm"
include "recnd.mm"
include "abscld.mm"
include "resqrtcld.mm"
include "absge0d.mm"
include "sqrtge0d.mm"
include "le2sqd.mm"
include "mpbird.mm"
include "remetdval.mm"
include "rrnmval.mm"
include "3expb.mm"
include "adantlr.mm"

theorem rrndstprj1
  let cA: class A
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cX: class X
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vz: setvar z
  let wph: wff ph
  let cJ: class J
  let cP: class P
  let cR: class R
  let vt: setvar t
  assume rrnval.1: |- X = ( RR ^m I )
  assume rrndstprj1.1: |- M = ( ( abs o. - ) |` ( RR X. RR ) )


  assert |- ( ( ( I e. Fin /\ A e. I ) /\ ( F e. X /\ G e. X ) ) -> ( ( F ` A ) M ( G ` A ) ) <_ ( F ( Rn ` I ) G ) )

  proof
    cI
    cfn
    wcel
    #
    cA
    cI
    wcel
    #
    wa
    #
    cF
    cX
    wcel
    #
    cG
    cX
    wcel
    #
    wa
    #
    wa
    #
    cA
    cF
    cfv
    #
    cA
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cI
    vk
    cv
    #
    cF
    cfv
    #
    @11
    cG
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    @7
    @8
    cM
    co
    #
    cF
    cG
    cI
    crrn
    cfv
    co
    #
    cle
    @6
    @10
    @17
    cle
    wbr
    @10
    c2
    cexp
    co
    #
    @17
    c2
    cexp
    co
    #
    cle
    wbr
    @6
    @9
    c2
    cexp
    co
    #
    @16
    @20
    @21
    cle
    @6
    cI
    @15
    @22
    vk
    cA
    @0
    @1
    @5
    simpll
    #
    @6
    @11
    cI
    wcel
    wa
    #
    @14
    @24
    @12
    @13
    @6
    cI
    cr
    @11
    cF
    @6
    cF
    cr
    cI
    cmap
    co
    #
    wcel
    cI
    cr
    cF
    wf
    @6
    cF
    cX
    @25
    @2
    @3
    @4
    simprl
    rrnval.1
    syl6eleq
    cF
    cr
    cI
    elmapi
    syl
    #
    ffvelrnda
    @6
    cI
    cr
    @11
    cG
    @6
    cG
    @25
    wcel
    cI
    cr
    cG
    wf
    @6
    cG
    cX
    @25
    @2
    @3
    @4
    simprr
    rrnval.1
    syl6eleq
    cG
    cr
    cI
    elmapi
    syl
    #
    ffvelrnda
    resubcld
    #
    resqcld
    #
    @24
    @14
    @28
    sqge0d
    #
    @11
    cA
    wceq
    #
    @14
    @9
    c2
    cexp
    @31
    @12
    @7
    @13
    @8
    cmin
    @11
    cA
    cF
    fveq2
    @11
    cA
    cG
    fveq2
    oveq12d
    oveq1d
    @0
    @1
    @5
    simplr
    #
    fsumge1
    @6
    @9
    cr
    wcel
    @20
    @22
    wceq
    @6
    @7
    @8
    @6
    cI
    cr
    cA
    cF
    @26
    @32
    ffvelrnd
    #
    @6
    cI
    cr
    cA
    cG
    @27
    @32
    ffvelrnd
    #
    resubcld
    #
    @9
    absresq
    syl
    @6
    @16
    cr
    wcel
    cc0
    @16
    cle
    wbr
    @21
    @16
    wceq
    @6
    cI
    @15
    vk
    @23
    @29
    fsumrecl
    #
    @6
    cI
    @15
    vk
    @23
    @29
    @30
    fsumge0
    #
    @16
    resqrtth
    syl2anc
    3brtr4d
    @6
    @10
    @17
    @6
    @9
    @6
    @9
    @35
    recnd
    #
    abscld
    @6
    @16
    @36
    @37
    resqrtcld
    @6
    @9
    @38
    absge0d
    @6
    @16
    @36
    @37
    sqrtge0d
    le2sqd
    mpbird
    @6
    @7
    cr
    wcel
    @8
    cr
    wcel
    @18
    @10
    wceq
    @33
    @34
    @7
    @8
    cM
    rrndstprj1.1
    remetdval
    syl2anc
    @0
    @5
    @19
    @17
    wceq
    #
    @1
    @0
    @3
    @4
    @39
    vk
    cF
    cG
    cI
    cX
    rrnval.1
    rrnmval
    3expb
    adantlr
    3brtr4d
end
