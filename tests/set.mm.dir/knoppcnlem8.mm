include "cn0.mm"
include "cc.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "caddc.mm"
include "cof.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc0.mm"
include "cseq.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "adantr.mm"
include "simpr.mm"
include "knoppcnlem7.mm"
include "cuz.mm"
include "simplr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "ad2antrr.mm"
include "elfznn0.mm"
include "adantl.mm"
include "knoppcnlem3.mm"
include "recnd.mm"
include "addcl.mm"
include "seqcl.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "reex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "eqeltrd.mm"
include "wfn.mm"
include "wceq.mm"
include "cz.mm"
include "0z.mm"
include "seqfn.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "dffn5.mm"
include "mpbi.mm"
include "feq1i.mm"

theorem knoppcnlem8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vw: setvar w
  assume knoppcnlem8.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcnlem8.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcnlem8.n: |- ( ph -> N e. NN )
  assume knoppcnlem8.1: |- ( ph -> C e. RR )

  disjoint C n
  disjoint C y
  disjoint n y
  disjoint F m
  disjoint F z
  disjoint m z
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint n ph
  disjoint ph y
  disjoint m ph
  disjoint F a
  disjoint F b
  disjoint F k
  disjoint F w
  disjoint a b
  disjoint a k
  disjoint a w
  disjoint b k
  disjoint b w
  disjoint k w
  disjoint k m
  disjoint k z
  disjoint m w
  disjoint w z
  disjoint a ph
  disjoint k ph
  disjoint ph w
  disjoint a n
  disjoint a y
  disjoint k n
  disjoint k y
  disjoint n w
  disjoint w y
  disjoint a x
  disjoint w x
  disjoint b ph
  assert |- ( ph -> seq 0 ( oF + , ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) ) ) : NN0 --> ( CC ^m RR ) )

  proof
    wph
    cn0
    cc
    cr
    cmap
    co
    #
    vk
    cn0
    vk
    cv
    #
    caddc
    cof
    #
    vm
    cn0
    vz
    cr
    vm
    cv
    vz
    cv
    cF
    cfv
    cfv
    cmpt
    cmpt
    #
    cc0
    cseq
    #
    cfv
    #
    cmpt
    #
    wf
    cn0
    @0
    @4
    wf
    wph
    vk
    cn0
    @5
    @0
    @6
    wph
    @1
    cn0
    wcel
    #
    wa
    #
    @5
    vw
    cr
    @1
    caddc
    vw
    cv
    #
    cF
    cfv
    #
    cc0
    cseq
    cfv
    #
    cmpt
    #
    @0
    @8
    vx
    vy
    vz
    vw
    cC
    cT
    vm
    vn
    cF
    @1
    cN
    knoppcnlem8.t
    knoppcnlem8.f
    wph
    cN
    cn
    wcel
    #
    @7
    knoppcnlem8.n
    adantr
    #
    wph
    cC
    cr
    wcel
    #
    @7
    knoppcnlem8.1
    adantr
    #
    wph
    @7
    simpr
    knoppcnlem7
    @8
    cr
    cc
    @12
    wf
    #
    @12
    @0
    wcel
    #
    @8
    vw
    cr
    @11
    cc
    @12
    @8
    @9
    cr
    wcel
    #
    wa
    #
    va
    vb
    caddc
    cc
    @10
    cc0
    @1
    @20
    @1
    cn0
    cc0
    cuz
    cfv
    #
    wph
    @7
    @19
    simplr
    nn0uz
    syl6eleq
    @20
    va
    cv
    #
    cc0
    @1
    cfz
    co
    wcel
    #
    wa
    #
    @22
    @10
    cfv
    @24
    vx
    vy
    @9
    cC
    cT
    vn
    cF
    @22
    cN
    knoppcnlem8.t
    knoppcnlem8.f
    @8
    @13
    @19
    @23
    @14
    ad2antrr
    @8
    @15
    @19
    @23
    @16
    ad2antrr
    @8
    @19
    @23
    simplr
    @23
    @22
    cn0
    wcel
    @20
    @22
    @1
    elfznn0
    adantl
    knoppcnlem3
    recnd
    @22
    cc
    wcel
    vb
    cv
    #
    cc
    wcel
    wa
    @22
    @25
    caddc
    co
    cc
    wcel
    @20
    @22
    @25
    addcl
    adantl
    seqcl
    @12
    eqid
    fmptd
    cc
    cvv
    wcel
    #
    cr
    cvv
    wcel
    #
    wa
    @18
    @17
    wb
    @26
    @27
    cnex
    reex
    pm3.2i
    cc
    cr
    @12
    cvv
    cvv
    elmapg
    ax-mp
    sylibr
    eqeltrd
    @6
    eqid
    fmptd
    cn0
    @0
    @4
    @6
    @4
    cn0
    wfn
    #
    @4
    @6
    wceq
    @28
    @4
    @21
    wfn
    #
    cc0
    cz
    wcel
    @29
    0z
    @2
    @3
    cc0
    seqfn
    ax-mp
    cn0
    @21
    @4
    nn0uz
    fneq2i
    mpbir
    vk
    cn0
    @4
    dffn5
    mpbi
    feq1i
    sylibr
end
