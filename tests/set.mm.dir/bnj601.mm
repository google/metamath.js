include "cv.mm"
include "wfn.mm"
include "wsbc.mm"
include "w3a.mm"
include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "com.mm"
include "w-bnj17.mm"
include "wel.mm"
include "wne.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "biid.mm"
include "wb.mm"
include "bnj602.mm"
include "cbviunv.mm"
include "opeq2i.mm"
include "sneqi.mm"
include "uneq2i.mm"
include "dfsbcq.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "eqid.mm"
include "bnj600.mm"

theorem bnj601
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vz: setvar z
  assume bnj601.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj601.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj601.3: |- D = ( _om \ { (/) } )
  assume bnj601.4: |- ( ch <-> ( ( R _FrSe A /\ x e. A ) -> E! f ( f Fn n /\ ph /\ ps ) ) )
  assume bnj601.5: |- ( th <-> A. m e. D ( m _E n -> [. m / n ]. ch ) )

  disjoint A f
  disjoint A i
  disjoint A m
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f m
  disjoint f n
  disjoint f y
  disjoint i m
  disjoint i n
  disjoint i y
  disjoint m n
  disjoint m y
  disjoint n y
  disjoint D f
  disjoint D i
  disjoint R f
  disjoint R i
  disjoint R m
  disjoint R n
  disjoint R y
  disjoint f x
  disjoint m x
  disjoint n x
  disjoint i ph
  disjoint m ph
  disjoint m ps
  disjoint A p
  disjoint f p
  disjoint i p
  disjoint m p
  disjoint n p
  disjoint p y
  disjoint A z
  disjoint f z
  disjoint i z
  disjoint p z
  disjoint y z
  disjoint D p
  disjoint R p
  disjoint R z
  disjoint p x
  disjoint p ph
  disjoint p ps
  disjoint p th
  assert |- ( n =/= 1o -> ( ( n e. D /\ th ) -> ch ) )

  proof
    wph
    wps
    wch
    wth
    vf
    cv
    #
    vm
    cv
    #
    wfn
    wph
    vn
    @1
    wsbc
    #
    wps
    vn
    @1
    wsbc
    #
    w3a
    #
    @1
    cD
    wcel
    #
    vn
    cv
    #
    @1
    csuc
    wceq
    #
    vp
    cv
    #
    com
    wcel
    @1
    @8
    csuc
    wceq
    w-bnj17
    #
    vi
    cv
    #
    com
    wcel
    #
    @10
    csuc
    #
    @6
    wcel
    #
    @1
    @12
    wceq
    w3a
    #
    @5
    @7
    vp
    vm
    wel
    w3a
    #
    @11
    @13
    @1
    @12
    wne
    w3a
    #
    vx
    vy
    cA
    vy
    @10
    @0
    cfv
    cA
    cR
    vy
    cv
    #
    c-bnj14
    #
    ciun
    #
    vy
    @8
    @0
    cfv
    #
    @18
    ciun
    #
    cD
    cR
    vf
    vi
    vm
    vn
    @0
    @1
    vz
    @20
    cA
    cR
    vz
    cv
    #
    c-bnj14
    #
    ciun
    #
    cop
    #
    csn
    #
    cun
    #
    vy
    @10
    @27
    cfv
    @18
    ciun
    #
    vy
    @8
    @27
    cfv
    @18
    ciun
    #
    vp
    @2
    @3
    wch
    vn
    @1
    wsbc
    #
    wph
    vf
    @0
    @1
    @21
    cop
    #
    csn
    #
    cun
    #
    wsbc
    #
    wps
    vf
    @33
    wsbc
    #
    wch
    vf
    @33
    wsbc
    #
    bnj601.1
    bnj601.2
    bnj601.3
    bnj601.4
    bnj601.5
    @2
    biid
    @3
    biid
    @30
    biid
    @33
    @27
    wceq
    #
    @34
    wph
    vf
    @27
    wsbc
    wb
    @32
    @26
    @0
    @31
    @25
    @21
    @24
    @1
    vy
    vz
    @20
    @18
    @23
    cA
    cR
    @17
    @22
    bnj602
    cbviunv
    opeq2i
    sneqi
    uneq2i
    #
    wph
    vf
    @33
    @27
    dfsbcq
    ax-mp
    @37
    @35
    wps
    vf
    @27
    wsbc
    wb
    @38
    wps
    vf
    @33
    @27
    dfsbcq
    ax-mp
    @37
    @36
    wch
    vf
    @27
    wsbc
    wb
    @38
    wch
    vf
    @33
    @27
    dfsbcq
    ax-mp
    @33
    @27
    @38
    eqcomi
    #
    @4
    biid
    @15
    biid
    @9
    biid
    @14
    biid
    @16
    biid
    @19
    eqid
    @21
    eqid
    @28
    eqid
    @29
    eqid
    @39
    bnj600
end
