include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "c-bnj14.mm"
include "wral.mm"
include "csn.mm"
include "c-bnj18.mm"
include "cun.mm"
include "wex.mm"
include "wn.mm"
include "wbr.mm"
include "bnj1212.mm"
include "snssd.mm"
include "bnj1147.mm"
include "a1i.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "wa.mm"
include "wceq.mm"
include "elsni.mm"
include "adantl.mm"
include "bnj602.mm"
include "syl.mm"
include "w-bnj15.mm"
include "c0.mm"
include "wne.mm"
include "simplbi.mm"
include "bnj835.mm"
include "bnj906.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "eqsstrd.mm"
include "ssun4.mm"
include "syl6sseqr.mm"
include "simpr.mm"
include "bnj1213.mm"
include "bnj1125.mm"
include "syl3anc.mm"
include "sstrd.mm"
include "wo.mm"
include "bnj1424.mm"
include "mpjaodan.mm"
include "ralrimiva.mm"
include "wsbc.mm"
include "cvv.mm"
include "wb.mm"
include "snex.mm"
include "bnj893.mm"
include "bnj1149.mm"
include "syl5eqel.mm"
include "bnj1454.mm"
include "weq.mm"
include "sseq1d.mm"
include "cbvralv.mm"
include "anbi2i.mm"
include "sbcbii.mm"
include "syl6bb.mm"
include "sseq1.mm"
include "sseq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "sbcieg.mm"
include "bitrd.mm"
include "mpbir2and.mm"

theorem bnj1452
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cH: class H
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  let bnjwtam: wff ta'
  assume bnj1452.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1452.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1452.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1452.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1452.5: |- D = { x e. A | -. E. f ta }
  assume bnj1452.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1452.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1452.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1452.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1452.10: |- P = U. H
  assume bnj1452.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1452.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1452.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.
  assume bnj1452.14: |- E = ( { x } u. _trCl ( x , A , R ) )

  disjoint A d
  disjoint A x
  disjoint A z
  disjoint d x
  disjoint d z
  disjoint x z
  disjoint E d
  disjoint E z
  disjoint R d
  disjoint R x
  disjoint R z
  disjoint ch z
  assert |- ( ch -> E e. B )

  proof
    wch
    cE
    cB
    wcel
    #
    cE
    cA
    wss
    #
    cA
    cR
    vz
    cv
    #
    c-bnj14
    #
    cE
    wss
    #
    vz
    cE
    wral
    #
    wch
    cE
    vx
    cv
    #
    csn
    #
    cA
    cR
    @6
    c-bnj18
    #
    cun
    #
    cA
    bnj1452.14
    wch
    @7
    @8
    cA
    wch
    @6
    cA
    wta
    vf
    wex
    wn
    wps
    wch
    vy
    cv
    @6
    cR
    wbr
    wn
    vy
    cD
    wral
    #
    vx
    cA
    cD
    bnj1452.5
    bnj1452.7
    bnj1212
    #
    snssd
    @8
    cA
    wss
    wch
    cA
    cR
    @6
    bnj1147
    #
    a1i
    unssd
    syl5eqss
    wch
    @4
    vz
    cE
    wch
    @2
    cE
    wcel
    #
    wa
    #
    @2
    @7
    wcel
    #
    @4
    @2
    @8
    wcel
    #
    @14
    @15
    wa
    #
    @3
    @8
    wss
    #
    @4
    @17
    @3
    cA
    cR
    @6
    c-bnj14
    #
    @8
    @17
    @2
    @6
    wceq
    #
    @3
    @19
    wceq
    @15
    @20
    @14
    @2
    @6
    elsni
    adantl
    cA
    cR
    @2
    @6
    bnj602
    syl
    wch
    @19
    @8
    wss
    #
    @13
    @15
    wch
    cA
    cR
    w-bnj15
    #
    @6
    cA
    wcel
    #
    @21
    wps
    @6
    cD
    wcel
    @10
    @22
    wch
    bnj1452.7
    wps
    @22
    cD
    c0
    wne
    bnj1452.6
    simplbi
    bnj835
    #
    @11
    cA
    cR
    @6
    bnj906
    syl2anc
    ad2antrr
    eqsstrd
    @18
    @3
    @9
    cE
    @3
    @8
    @7
    ssun4
    bnj1452.14
    syl6sseqr
    #
    syl
    @14
    @16
    wa
    #
    @18
    @4
    @26
    @3
    cA
    cR
    @2
    c-bnj18
    #
    @8
    @26
    @22
    @2
    cA
    wcel
    @3
    @27
    wss
    wch
    @22
    @13
    @16
    @24
    ad2antrr
    #
    @26
    vz
    @8
    cA
    @12
    @14
    @16
    simpr
    #
    bnj1213
    cA
    cR
    @2
    bnj906
    syl2anc
    @26
    @22
    @23
    @16
    @27
    @8
    wss
    @28
    wch
    @23
    @13
    @16
    @11
    ad2antrr
    @29
    cA
    cR
    @6
    @2
    bnj1125
    syl3anc
    sstrd
    @25
    syl
    @13
    @15
    @16
    wo
    wch
    cE
    @7
    @8
    @2
    bnj1452.14
    bnj1424
    adantl
    mpjaodan
    ralrimiva
    wch
    @0
    vd
    cv
    #
    cA
    wss
    #
    @3
    @30
    wss
    #
    vz
    @30
    wral
    #
    wa
    #
    vd
    cE
    wsbc
    #
    @1
    @5
    wa
    #
    wch
    @0
    @31
    @19
    @30
    wss
    #
    vx
    @30
    wral
    #
    wa
    #
    vd
    cE
    wsbc
    #
    @35
    wch
    cE
    cvv
    wcel
    #
    @0
    @40
    wb
    wch
    cE
    @9
    cvv
    bnj1452.14
    wch
    @7
    @8
    @7
    cvv
    wcel
    wch
    @6
    snex
    a1i
    wch
    @22
    @23
    @8
    cvv
    wcel
    @24
    @11
    cA
    cR
    @6
    bnj893
    syl2anc
    bnj1149
    syl5eqel
    #
    @39
    vd
    cB
    cE
    bnj1452.1
    bnj1454
    syl
    @39
    @34
    vd
    cE
    @38
    @33
    @31
    @37
    @32
    vx
    vz
    @30
    vx
    vz
    weq
    @19
    @3
    @30
    cA
    cR
    @6
    @2
    bnj602
    sseq1d
    cbvralv
    anbi2i
    sbcbii
    syl6bb
    wch
    @41
    @35
    @36
    wb
    @42
    @34
    @36
    vd
    cE
    cvv
    @30
    cE
    wceq
    @31
    @1
    @33
    @5
    @30
    cE
    cA
    sseq1
    @32
    @4
    vz
    @30
    cE
    @30
    cE
    @3
    sseq2
    raleqbi1dv
    anbi12d
    sbcieg
    syl
    bitrd
    mpbir2and
end
