include "cv.mm"
include "wcel.mm"
include "com.mm"
include "wss.mm"
include "wa.mm"
include "coe.mm"
include "co.mm"
include "cfv.mm"
include "wf1o.mm"
include "con0.mm"
include "c1o.mm"
include "cdif.mm"
include "wrex.mm"
include "wi.mm"
include "r19.21bi.mm"
include "impr.mm"
include "simpr.mm"
include "crn.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wceq.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "wfo.mm"
include "f1ofo.mm"
include "ad2antll.mm"
include "forn.mm"
include "syl.mm"
include "eqtr4d.mm"
include "cvv.mm"
include "wf1.mm"
include "2a1i.mm"
include "wb.mm"
include "c2o.mm"
include "omelon.mm"
include "1onn.mm"
include "ondif2.mm"
include "mpbir2an.mm"
include "a1i.mm"
include "eldifi.mm"
include "oecan.mm"
include "syl3anc.mm"
include "ex.mm"
include "dom2lem.mm"
include "f1f1orn.mm"
include "simprl.mm"
include "f1ocnvfv.mm"
include "syl2anc.mm"
include "mpd.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "oveq2d.mm"
include "f1oeq3.mm"
include "anbi12d.mm"
include "mpbird.mm"
include "rexlimddv.mm"

theorem infxpenc2lem1
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let vn: setvar n
  let cW: class W
  let vb: setvar b
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  assume infxpenc2.1: |- ( ph -> A e. On )
  assume infxpenc2.2: |- ( ph -> A. b e. A ( _om C_ b -> E. w e. ( On \ 1o ) ( n ` b ) : b -1-1-onto-> ( _om ^o w ) ) )
  assume infxpenc2.3: |- W = ( `' ( x e. ( On \ 1o ) |-> ( _om ^o x ) ) ` ran ( n ` b ) )

  disjoint b n
  disjoint b w
  disjoint b x
  disjoint A b
  disjoint n w
  disjoint n x
  disjoint A n
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint b ph
  disjoint ph w
  disjoint ph x
  disjoint W w
  disjoint W x
  disjoint b g
  disjoint b y
  disjoint g n
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint n y
  disjoint w y
  disjoint x y
  disjoint A y
  disjoint ph y
  disjoint g z
  disjoint W g
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint W y
  disjoint W z
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint G g
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ( ph /\ ( b e. A /\ _om C_ b ) ) -> ( W e. ( On \ 1o ) /\ ( n ` b ) : b -1-1-onto-> ( _om ^o W ) ) )

  proof
    wph
    vb
    cv
    #
    cA
    wcel
    #
    com
    @0
    wss
    #
    wa
    wa
    #
    @0
    com
    vw
    cv
    #
    coe
    co
    #
    @0
    vn
    cv
    cfv
    #
    wf1o
    #
    cW
    con0
    c1o
    cdif
    #
    wcel
    #
    @0
    com
    cW
    coe
    co
    #
    @6
    wf1o
    #
    wa
    #
    vw
    @8
    wph
    @1
    @2
    @7
    vw
    @8
    wrex
    #
    wph
    @2
    @13
    wi
    vb
    cA
    infxpenc2.2
    r19.21bi
    impr
    @3
    @4
    @8
    wcel
    #
    @7
    wa
    #
    wa
    #
    @12
    @15
    @3
    @15
    simpr
    @16
    @9
    @14
    @11
    @7
    @16
    cW
    @4
    @8
    @16
    cW
    @6
    crn
    #
    vx
    @8
    com
    vx
    cv
    #
    coe
    co
    #
    cmpt
    #
    ccnv
    cfv
    #
    @4
    infxpenc2.3
    @16
    @4
    @20
    cfv
    #
    @17
    wceq
    #
    @21
    @4
    wceq
    #
    @16
    @22
    @5
    @17
    @14
    @22
    @5
    wceq
    @3
    @7
    vx
    @4
    @19
    @5
    @8
    @20
    @18
    @4
    com
    coe
    oveq2
    @20
    eqid
    com
    @4
    coe
    ovex
    fvmpt
    ad2antrl
    @16
    @0
    @5
    @6
    wfo
    #
    @17
    @5
    wceq
    @7
    @25
    @3
    @14
    @0
    @5
    @6
    f1ofo
    ad2antll
    @0
    @5
    @6
    forn
    syl
    eqtr4d
    @16
    @8
    @20
    crn
    #
    @20
    wf1o
    #
    @14
    @23
    @24
    wi
    @16
    @8
    cvv
    @20
    wf1
    @27
    @16
    vx
    vy
    @8
    cvv
    @19
    com
    vy
    cv
    #
    coe
    co
    #
    @19
    cvv
    wcel
    @16
    @18
    @8
    wcel
    #
    com
    @18
    coe
    ovex
    2a1i
    @16
    @30
    @28
    @8
    wcel
    #
    wa
    #
    @19
    @29
    wceq
    @18
    @28
    wceq
    wb
    #
    @16
    @32
    wa
    #
    com
    con0
    c2o
    cdif
    wcel
    #
    @18
    con0
    wcel
    #
    @28
    con0
    wcel
    #
    @33
    @35
    @34
    @35
    com
    con0
    wcel
    c1o
    com
    wcel
    omelon
    1onn
    com
    ondif2
    mpbir2an
    a1i
    @30
    @36
    @16
    @31
    @18
    con0
    c1o
    eldifi
    ad2antrl
    @31
    @37
    @16
    @30
    @28
    con0
    c1o
    eldifi
    ad2antll
    com
    @18
    @28
    oecan
    syl3anc
    ex
    dom2lem
    @8
    cvv
    @20
    f1f1orn
    syl
    @3
    @14
    @7
    simprl
    @8
    @26
    @4
    @17
    @20
    f1ocnvfv
    syl2anc
    mpd
    syl5eq
    #
    eleq1d
    @16
    @10
    @5
    wceq
    @11
    @7
    wb
    @16
    cW
    @4
    com
    coe
    @38
    oveq2d
    @10
    @5
    @0
    @6
    f1oeq3
    syl
    anbi12d
    mpbird
    rexlimddv
end
