include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "caddc.mm"
include "cc.mm"
include "cc0.mm"
include "cv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "addid2.mm"
include "adantl.mm"
include "0cnd.mm"
include "adantr.mm"
include "cz.mm"
include "wf.mm"
include "cif.mm"
include "iftrue.mm"
include "eqeltrd.mm"
include "ex.mm"
include "wn.mm"
include "iffalse.mm"
include "0cn.mm"
include "syl6eqel.mm"
include "pm2.61d1.mm"
include "fmptd.mm"
include "eluzelz.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cdif.mm"
include "elfzelz.mm"
include "simplr.mm"
include "zcnd.mm"
include "ad2antrr.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "sseqtr4d.mm"
include "fznuz.mm"
include "ssneldd.mm"
include "eldifd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eldifi.mm"
include "eldifn.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "vtoclga.mm"
include "seqid.mm"

theorem sumrblem
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
  assert |- ( ( ph /\ A C_ ( ZZ>= ` N ) ) -> ( seq M ( + , F ) |` ( ZZ>= ` N ) ) = seq N ( + , F ) )

  proof
    wph
    cA
    cN
    cuz
    cfv
    #
    wss
    #
    wa
    #
    vn
    caddc
    cc
    cF
    cM
    cN
    cc0
    vn
    cv
    #
    cc
    wcel
    cc0
    @3
    caddc
    co
    @3
    wceq
    @2
    @3
    addid2
    adantl
    @2
    0cnd
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    @1
    sumrb.3
    adantr
    @2
    cz
    cc
    cN
    cF
    wph
    cz
    cc
    cF
    wf
    @1
    wph
    vk
    cz
    vk
    cv
    #
    cA
    wcel
    #
    cB
    cc0
    cif
    #
    cc
    cF
    wph
    @7
    cc
    wcel
    #
    @5
    cz
    wcel
    #
    wph
    @6
    @8
    wph
    @6
    @8
    wph
    @6
    wa
    @7
    cB
    cc
    @6
    @7
    cB
    wceq
    wph
    @6
    cB
    cc0
    iftrue
    adantl
    summo.2
    eqeltrd
    ex
    @6
    wn
    #
    @7
    cc0
    cc
    @6
    cB
    cc0
    iffalse
    #
    0cn
    syl6eqel
    pm2.61d1
    adantr
    summo.1
    fmptd
    adantr
    wph
    cN
    cz
    wcel
    #
    @1
    wph
    @4
    @12
    sumrb.3
    cM
    cN
    eluzelz
    syl
    #
    adantr
    ffvelrnd
    @2
    @3
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    @3
    cz
    cA
    cdif
    #
    wcel
    @3
    cF
    cfv
    #
    cc0
    wceq
    #
    @16
    @3
    cz
    cA
    @15
    @3
    cz
    wcel
    @2
    @3
    cM
    @14
    elfzelz
    adantl
    @16
    cA
    @14
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @3
    @16
    cA
    @0
    @21
    wph
    @1
    @15
    simplr
    @16
    @20
    cN
    cuz
    @16
    cN
    cc
    wcel
    #
    c1
    cc
    wcel
    @20
    cN
    wceq
    wph
    @22
    @1
    @15
    wph
    cN
    @13
    zcnd
    ad2antrr
    ax-1cn
    cN
    c1
    npcan
    sylancl
    fveq2d
    sseqtr4d
    @15
    @3
    @21
    wcel
    wn
    @2
    @3
    cM
    @14
    fznuz
    adantl
    ssneldd
    eldifd
    @5
    cF
    cfv
    #
    cc0
    wceq
    @19
    vk
    @3
    @17
    @5
    @3
    wceq
    @23
    @18
    cc0
    @5
    @3
    cF
    fveq2
    eqeq1d
    @5
    @17
    wcel
    #
    @23
    @7
    cc0
    @24
    @9
    @8
    @23
    @7
    wceq
    @5
    cz
    cA
    eldifi
    @24
    @7
    cc0
    cc
    @24
    @10
    @7
    cc0
    wceq
    @5
    cz
    cA
    eldifn
    @11
    syl
    #
    0cn
    syl6eqel
    vk
    cz
    @7
    cc
    cF
    summo.1
    fvmpt2
    syl2anc
    @25
    eqtrd
    vtoclga
    syl
    seqid
end
