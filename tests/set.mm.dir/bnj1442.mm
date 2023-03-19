include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "wcel.mm"
include "wceq.mm"
include "wfun.mm"
include "cop.mm"
include "c-bnj18.mm"
include "cun.mm"
include "bnj930.mm"
include "opex.mm"
include "snid.mm"
include "elun2.mm"
include "ax-mp.mm"
include "eleqtrri.mm"
include "funopfv.mm"
include "mpisyl.mm"
include "bnj832.mm"
include "elsni.mm"
include "simplbiim.mm"
include "fveq2d.mm"
include "c-bnj14.mm"
include "cres.mm"
include "bnj602.mm"
include "reseq2d.mm"
include "syl.mm"
include "wss.mm"
include "bnj931.mm"
include "a1i.mm"
include "cdm.mm"
include "w-bnj15.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "simplbi.mm"
include "bnj835.mm"
include "wex.mm"
include "bnj1212.mm"
include "bnj906.mm"
include "syl2anc.mm"
include "wfn.mm"
include "fndm.mm"
include "sseqtr4d.mm"
include "bnj1503.mm"
include "eqtrd.mm"
include "opeq12d.mm"
include "3eqtr4g.mm"
include "3eqtr4d.mm"

theorem bnj1442
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
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
  assume bnj1442.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1442.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1442.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1442.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1442.5: |- D = { x e. A | -. E. f ta }
  assume bnj1442.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1442.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1442.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1442.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1442.10: |- P = U. H
  assume bnj1442.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1442.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1442.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.
  assume bnj1442.14: |- E = ( { x } u. _trCl ( x , A , R ) )
  assume bnj1442.15: |- ( ch -> P Fn _trCl ( x , A , R ) )
  assume bnj1442.16: |- ( ch -> Q Fn ( { x } u. _trCl ( x , A , R ) ) )
  assume bnj1442.17: |- ( th <-> ( ch /\ z e. E ) )
  assume bnj1442.18: |- ( et <-> ( th /\ z e. { x } ) )

  disjoint A x
  assert |- ( et -> ( Q ` z ) = ( G ` W ) )

  proof
    wet
    vx
    cv
    #
    cQ
    cfv
    #
    cZ
    cG
    cfv
    #
    vz
    cv
    #
    cQ
    cfv
    cW
    cG
    cfv
    wth
    @3
    @0
    csn
    #
    wcel
    #
    @1
    @2
    wceq
    #
    wet
    bnj1442.18
    wch
    @3
    cE
    wcel
    #
    @6
    wth
    bnj1442.17
    wch
    cQ
    wfun
    @0
    @2
    cop
    #
    cQ
    wcel
    @6
    wch
    @4
    cA
    cR
    @0
    c-bnj18
    #
    cun
    cQ
    bnj1442.16
    bnj930
    #
    @8
    cP
    @8
    csn
    #
    cun
    #
    cQ
    @8
    @11
    wcel
    @8
    @12
    wcel
    @8
    @0
    @2
    opex
    snid
    @8
    @11
    cP
    elun2
    ax-mp
    bnj1442.12
    eleqtrri
    @0
    @2
    cQ
    funopfv
    mpisyl
    bnj832
    bnj832
    wet
    @3
    @0
    cQ
    wet
    wth
    @5
    @3
    @0
    wceq
    #
    bnj1442.18
    @3
    @0
    elsni
    simplbiim
    #
    fveq2d
    wet
    cW
    cZ
    cG
    wet
    @3
    cQ
    cA
    cR
    @3
    c-bnj14
    #
    cres
    #
    cop
    @0
    cP
    cA
    cR
    @0
    c-bnj14
    #
    cres
    #
    cop
    cW
    cZ
    wet
    @3
    @0
    @16
    @18
    @14
    wet
    @16
    cQ
    @17
    cres
    #
    @18
    wet
    @13
    @16
    @19
    wceq
    @14
    @13
    @15
    @17
    cQ
    cA
    cR
    @3
    @0
    bnj602
    reseq2d
    syl
    wth
    @5
    @19
    @18
    wceq
    #
    wet
    bnj1442.18
    wch
    @7
    @20
    wth
    bnj1442.17
    wch
    @17
    cQ
    cP
    @10
    cP
    cQ
    wss
    wch
    cQ
    cP
    @11
    bnj1442.12
    bnj931
    a1i
    wch
    @17
    @9
    cP
    cdm
    #
    wch
    cA
    cR
    w-bnj15
    #
    @0
    cA
    wcel
    @17
    @9
    wss
    wps
    @0
    cD
    wcel
    vy
    cv
    @0
    cR
    wbr
    wn
    vy
    cD
    wral
    #
    @22
    wch
    bnj1442.7
    wps
    @22
    cD
    c0
    wne
    bnj1442.6
    simplbi
    bnj835
    wta
    vf
    wex
    wn
    wps
    wch
    @23
    vx
    cA
    cD
    bnj1442.5
    bnj1442.7
    bnj1212
    cA
    cR
    @0
    bnj906
    syl2anc
    wch
    cP
    @9
    wfn
    @21
    @9
    wceq
    bnj1442.15
    @9
    cP
    fndm
    syl
    sseqtr4d
    bnj1503
    bnj832
    bnj832
    eqtrd
    opeq12d
    bnj1442.13
    bnj1442.11
    3eqtr4g
    fveq2d
    3eqtr4d
end
