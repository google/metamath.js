include "cgsu.mm"
include "co.mm"
include "crn.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "cfz.mm"
include "wcel.mm"
include "cseq.mm"
include "cfv.mm"
include "cuz.mm"
include "wrex.mm"
include "wex.mm"
include "cio.mm"
include "c1.mm"
include "chash.mm"
include "wf1o.mm"
include "ccom.mm"
include "cif.mm"
include "cmnd.mm"
include "eqid.mm"
include "csupp.mm"
include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "a1i.mm"
include "wf.mm"
include "jca.mm"
include "fex.mm"
include "syl.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppimacnv.mm"
include "sylancl.mm"
include "gsumvallem2.mm"
include "eqcomd.mm"
include "difeq2d.mm"
include "imaeq2d.mm"
include "3eqtrd.mm"
include "gsumval.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "sseq2d.mm"
include "adantr.mm"
include "cin.mm"
include "wfn.mm"
include "ffn.mm"
include "simpr.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "disjdif.mm"
include "fimacnvdisj.mm"
include "ex.mm"
include "sylbid.mm"
include "necon3ad.mm"
include "mpd.mm"
include "iffalsed.mm"

theorem gsumval3a
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cH: class H
  assume gsumval3.b: |- B = ( Base ` G )
  assume gsumval3.0: |- .0. = ( 0g ` G )
  assume gsumval3.p: |- .+ = ( +g ` G )
  assume gsumval3.z: |- Z = ( Cntz ` G )
  assume gsumval3.g: |- ( ph -> G e. Mnd )
  assume gsumval3.a: |- ( ph -> A e. V )
  assume gsumval3.f: |- ( ph -> F : A --> B )
  assume gsumval3.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumval3a.t: |- ( ph -> W e. Fin )
  assume gsumval3a.n: |- ( ph -> W =/= (/) )
  assume gsumval3a.w: |- W = ( F supp .0. )
  assume gsumval3a.i: |- ( ph -> -. A e. ran ... )

  disjoint f x
  disjoint .+ f
  disjoint .+ x
  disjoint A f
  disjoint A x
  disjoint f ph
  disjoint ph x
  disjoint .0. x
  disjoint G f
  disjoint G x
  disjoint V x
  disjoint B f
  disjoint B x
  disjoint F f
  disjoint F x
  disjoint W f
  disjoint W x
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .+ g
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint .+ k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint .+ m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint .+ n
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint A g
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A y
  disjoint A z
  disjoint g ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint ph z
  disjoint .0. g
  disjoint .0. y
  disjoint .0. z
  disjoint G g
  disjoint G m
  disjoint G n
  disjoint G y
  disjoint G z
  disjoint M f
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint B g
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B y
  disjoint B z
  disjoint F g
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F y
  disjoint F z
  disjoint H f
  disjoint H g
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint W g
  disjoint W k
  disjoint W m
  disjoint W n
  disjoint W y
  disjoint W z
  assert |- ( ph -> ( G gsum F ) = ( iota x E. f ( f : ( 1 ... ( # ` W ) ) -1-1-onto-> W /\ x = ( seq 1 ( .+ , ( F o. f ) ) ` ( # ` W ) ) ) ) )

  proof
    wph
    cG
    cF
    cgsu
    co
    cF
    crn
    #
    vz
    cv
    #
    vy
    cv
    #
    c.pl
    co
    @2
    wceq
    @2
    @1
    c.pl
    co
    @2
    wceq
    wa
    vy
    cB
    wral
    vz
    cB
    crab
    #
    wss
    #
    c.0
    cA
    cfz
    crn
    wcel
    #
    cA
    vm
    cv
    #
    vn
    cv
    #
    cfz
    co
    wceq
    vx
    cv
    #
    @7
    c.pl
    cF
    @6
    cseq
    cfv
    wceq
    wa
    vn
    @6
    cuz
    cfv
    wrex
    vm
    wex
    vx
    cio
    #
    c1
    cW
    chash
    cfv
    #
    cfz
    co
    cW
    vf
    cv
    #
    wf1o
    @8
    @10
    c.pl
    cF
    @11
    ccom
    c1
    cseq
    cfv
    wceq
    wa
    vf
    wex
    vx
    cio
    #
    cif
    #
    cif
    @13
    @12
    wph
    vx
    vy
    cA
    cB
    c.pl
    vf
    vm
    vn
    cF
    cG
    @3
    cmnd
    cW
    cV
    c.0
    vz
    gsumval3.b
    gsumval3.0
    gsumval3.p
    @3
    eqid
    #
    wph
    cW
    cF
    c.0
    csupp
    co
    #
    cF
    ccnv
    #
    cvv
    c.0
    csn
    #
    cdif
    #
    cima
    #
    @16
    cvv
    @3
    cdif
    #
    cima
    cW
    @15
    wceq
    #
    wph
    gsumval3a.w
    a1i
    wph
    cF
    cvv
    wcel
    #
    c.0
    cvv
    wcel
    #
    @15
    @19
    wceq
    #
    wph
    cA
    cB
    cF
    wf
    #
    cA
    cV
    wcel
    #
    wa
    #
    @22
    wph
    @25
    @26
    gsumval3.f
    gsumval3.a
    jca
    #
    cA
    cB
    cV
    cF
    fex
    #
    syl
    c.0
    cG
    c0g
    cfv
    cvv
    gsumval3.0
    cG
    c0g
    fvex
    eqeltri
    #
    cF
    cvv
    cvv
    c.0
    suppimacnv
    #
    sylancl
    wph
    @18
    @20
    @16
    wph
    @17
    @3
    cvv
    wph
    @3
    @17
    wph
    cG
    cmnd
    wcel
    @3
    @17
    wceq
    gsumval3.g
    vz
    vy
    cB
    c.pl
    cG
    @3
    c.0
    gsumval3.b
    gsumval3.0
    gsumval3.p
    @14
    gsumvallem2
    syl
    #
    eqcomd
    difeq2d
    imaeq2d
    3eqtrd
    gsumval3.g
    gsumval3.a
    gsumval3.f
    gsumval
    wph
    @4
    c.0
    @13
    wph
    cW
    c0
    wne
    @4
    wn
    gsumval3a.n
    wph
    @4
    cW
    c0
    wph
    @4
    @0
    @17
    wss
    #
    cW
    c0
    wceq
    #
    wph
    @3
    @17
    @0
    @32
    sseq2d
    wph
    @33
    @34
    wph
    @33
    wa
    #
    cW
    @15
    @19
    c0
    @21
    @35
    gsumval3a.w
    a1i
    @35
    @22
    @23
    @24
    @35
    @27
    @22
    wph
    @27
    @33
    @28
    adantr
    @29
    syl
    @30
    @31
    sylancl
    @35
    cA
    @17
    cF
    wf
    #
    @17
    @18
    cin
    c0
    wceq
    @19
    c0
    wceq
    @35
    cF
    cA
    wfn
    #
    @33
    @36
    wph
    @37
    @33
    wph
    @25
    @37
    gsumval3.f
    cA
    cB
    cF
    ffn
    syl
    adantr
    wph
    @33
    simpr
    cA
    @17
    cF
    df-f
    sylanbrc
    @17
    cvv
    disjdif
    cA
    @17
    @18
    cF
    fimacnvdisj
    sylancl
    3eqtrd
    ex
    sylbid
    necon3ad
    mpd
    iffalsed
    wph
    @5
    @9
    @12
    gsumval3a.i
    iffalsed
    3eqtrd
end
