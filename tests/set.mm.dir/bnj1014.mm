include "cv.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "c-bnj18.mm"
include "wss.mm"
include "wi.mm"
include "wfn.mm"
include "w3a.mm"
include "wrex.mm"
include "cab.mm"
include "nfcv.mm"
include "bnj911.mm"
include "nf5i.mm"
include "nfrex.mm"
include "nfab.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "nfv.mm"
include "nfan.mm"
include "nfim.mm"
include "nf5ri.mm"
include "wb.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "equcoms.mm"
include "bnj1317.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "fveq1.mm"
include "ciun.mm"
include "ssiun2.mm"
include "bnj882.mm"
include "syl6sseqr.mm"
include "sylan9ssr.mm"
include "chvar.mm"
include "spei.mm"
include "bnj1131.mm"

theorem bnj1014
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cX: class X
  assume bnj1014.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1014.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1014.13: |- D = ( _om \ { (/) } )
  assume bnj1014.14: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }

  disjoint A f
  disjoint A i
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f n
  disjoint f y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint D i
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint f g
  disjoint g i
  disjoint i j
  disjoint i ph
  assert |- ( ( g e. B /\ j e. dom g ) -> ( g ` j ) C_ _trCl ( X , A , R ) )

  proof
    vg
    cv
    #
    cB
    wcel
    #
    vj
    cv
    #
    @0
    cdm
    #
    wcel
    #
    wa
    #
    @2
    @0
    cfv
    #
    cA
    cR
    cX
    c-bnj18
    #
    wss
    #
    wi
    #
    vi
    @9
    vi
    @5
    @8
    vi
    @1
    @4
    vi
    vi
    vg
    cB
    vi
    cB
    vf
    cv
    #
    vn
    cv
    wfn
    wph
    wps
    w3a
    #
    vn
    cD
    wrex
    #
    vf
    cab
    bnj1014.14
    @12
    vi
    vf
    @11
    vi
    vn
    cD
    vi
    cD
    nfcv
    @11
    vi
    wph
    wps
    vy
    cA
    cR
    vf
    vi
    vn
    cX
    bnj1014.1
    bnj1014.2
    bnj911
    nf5i
    nfrex
    nfab
    nfcxfr
    nfcri
    @4
    vi
    nfv
    nfan
    @8
    vi
    nfv
    nfim
    nf5ri
    @9
    @1
    vi
    cv
    #
    @3
    wcel
    #
    wa
    #
    @13
    @0
    cfv
    #
    @7
    wss
    #
    wi
    #
    vi
    vj
    @9
    @18
    wb
    vj
    vi
    vj
    vi
    weq
    #
    @5
    @15
    @8
    @17
    @19
    @4
    @14
    @1
    @2
    @13
    @3
    eleq1
    anbi2d
    @19
    @6
    @16
    @7
    @2
    @13
    @0
    fveq2
    sseq1d
    imbi12d
    equcoms
    @10
    cB
    wcel
    #
    @13
    @10
    cdm
    #
    wcel
    #
    wa
    #
    @13
    @10
    cfv
    #
    @7
    wss
    #
    wi
    @18
    vf
    vg
    @15
    @17
    vf
    @1
    @14
    vf
    @1
    vf
    @12
    vf
    vg
    cB
    bnj1014.14
    bnj1317
    nf5i
    @14
    vf
    nfv
    nfan
    @17
    vf
    nfv
    nfim
    vf
    vg
    weq
    #
    @23
    @15
    @25
    @17
    @26
    @20
    @1
    @22
    @14
    @10
    @0
    cB
    eleq1
    @26
    @21
    @3
    @13
    @10
    @0
    dmeq
    eleq2d
    anbi12d
    @26
    @24
    @16
    @7
    @13
    @10
    @0
    fveq1
    sseq1d
    imbi12d
    @22
    @20
    @24
    vi
    @21
    @24
    ciun
    #
    @7
    vi
    @21
    @24
    ssiun2
    @20
    @27
    vf
    cB
    @27
    ciun
    @7
    vf
    cB
    @27
    ssiun2
    wph
    wps
    vy
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cX
    bnj1014.1
    bnj1014.2
    bnj1014.13
    bnj1014.14
    bnj882
    syl6sseqr
    sylan9ssr
    chvar
    spei
    bnj1131
end
