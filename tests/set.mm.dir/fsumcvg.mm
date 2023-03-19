include "caddc.mm"
include "cseq.mm"
include "cfv.mm"
include "cvv.mm"
include "cuz.mm"
include "eqid.mm"
include "wcel.mm"
include "cz.mm"
include "eluzelz.mm"
include "syl.mm"
include "seqex.mm"
include "a1i.mm"
include "cc.mm"
include "eluzel2.mm"
include "cv.mm"
include "wa.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "ex.mm"
include "wn.mm"
include "iffalse.mm"
include "0cn.mm"
include "syl6eqel.mm"
include "pm2.61d1.mm"
include "fvmpt2.mm"
include "syl2anr.mm"
include "adantr.mm"
include "serf.mm"
include "ffvelrnd.mm"
include "co.mm"
include "addid1.mm"
include "simpr.mm"
include "c1.mm"
include "cfz.mm"
include "elfzuz.mm"
include "cdif.mm"
include "sseld.mm"
include "fznuz.mm"
include "syl6.mm"
include "con2d.mm"
include "imp.mm"
include "eldifd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eldifi.mm"
include "eldifn.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "vtoclga.mm"
include "sylan2.mm"
include "adantlr.mm"
include "seqid2.mm"
include "eqcomd.mm"
include "climconst.mm"

theorem fsumcvg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cH: class H
  let cK: class K
  assume summo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 0 ) )
  assume summo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume sumrb.3: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fsumcvg.4: |- ( ph -> A C_ ( M ... N ) )

  disjoint A k
  disjoint F k
  disjoint N k
  disjoint k ph
  disjoint M k
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F f
  disjoint F g
  disjoint F j
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint G g
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint H i
  disjoint H x
  disjoint K i
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint N m
  disjoint N n
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint B f
  disjoint B j
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  assert |- ( ph -> seq M ( + , F ) ~~> ( seq M ( + , F ) ` N ) )

  proof
    wph
    cN
    caddc
    cF
    cM
    cseq
    #
    cfv
    #
    vn
    @0
    cN
    cvv
    cN
    cuz
    cfv
    #
    @2
    eqid
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    sumrb.3
    cM
    cN
    eluzelz
    syl
    @0
    cvv
    wcel
    wph
    caddc
    cF
    cM
    seqex
    a1i
    wph
    @3
    cc
    cN
    @0
    wph
    vk
    cF
    cM
    @3
    @3
    eqid
    wph
    @4
    cM
    cz
    wcel
    sumrb.3
    cM
    cN
    eluzel2
    syl
    wph
    vk
    cv
    #
    @3
    wcel
    #
    wa
    @5
    cF
    cfv
    #
    @5
    cA
    wcel
    #
    cB
    cc0
    cif
    #
    cc
    @6
    @5
    cz
    wcel
    #
    @9
    cc
    wcel
    #
    @7
    @9
    wceq
    #
    wph
    cM
    @5
    eluzelz
    wph
    @8
    @11
    wph
    @8
    @11
    wph
    @8
    wa
    @9
    cB
    cc
    @8
    @9
    cB
    wceq
    wph
    @8
    cB
    cc0
    iftrue
    adantl
    summo.2
    eqeltrd
    ex
    @8
    wn
    #
    @9
    cc0
    cc
    @8
    cB
    cc0
    iffalse
    #
    0cn
    syl6eqel
    pm2.61d1
    #
    vk
    cz
    @9
    cc
    cF
    summo.1
    fvmpt2
    #
    syl2anr
    wph
    @11
    @6
    @15
    adantr
    eqeltrd
    serf
    sumrb.3
    ffvelrnd
    #
    wph
    vn
    cv
    #
    @2
    wcel
    #
    wa
    #
    @1
    @18
    @0
    cfv
    @20
    vm
    caddc
    cc
    cF
    cN
    cM
    @18
    cc0
    vm
    cv
    #
    cc
    wcel
    @21
    cc0
    caddc
    co
    @21
    wceq
    @20
    @21
    addid1
    adantl
    wph
    @4
    @19
    sumrb.3
    adantr
    wph
    @19
    simpr
    wph
    @1
    cc
    wcel
    @19
    @17
    adantr
    wph
    @21
    cN
    c1
    caddc
    co
    #
    @18
    cfz
    co
    wcel
    #
    @21
    cF
    cfv
    #
    cc0
    wceq
    #
    @19
    @23
    wph
    @21
    @22
    cuz
    cfv
    wcel
    #
    @25
    @21
    @22
    @18
    elfzuz
    wph
    @26
    wa
    #
    @21
    cz
    cA
    cdif
    #
    wcel
    @25
    @27
    @21
    cz
    cA
    @26
    @21
    cz
    wcel
    wph
    @22
    @21
    eluzelz
    adantl
    wph
    @26
    @21
    cA
    wcel
    #
    wn
    wph
    @29
    @26
    wph
    @29
    @21
    cM
    cN
    cfz
    co
    #
    wcel
    @26
    wn
    wph
    cA
    @30
    @21
    fsumcvg.4
    sseld
    @21
    cM
    cN
    fznuz
    syl6
    con2d
    imp
    eldifd
    @7
    cc0
    wceq
    @25
    vk
    @21
    @28
    @5
    @21
    wceq
    @7
    @24
    cc0
    @5
    @21
    cF
    fveq2
    eqeq1d
    @5
    @28
    wcel
    #
    @7
    @9
    cc0
    @31
    @10
    @11
    @12
    @5
    cz
    cA
    eldifi
    @31
    @9
    cc0
    cc
    @31
    @13
    @9
    cc0
    wceq
    @5
    cz
    cA
    eldifn
    @14
    syl
    #
    0cn
    syl6eqel
    @16
    syl2anc
    @32
    eqtrd
    vtoclga
    syl
    sylan2
    adantlr
    seqid2
    eqcomd
    climconst
end
