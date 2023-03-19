include "cdm.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "c-bnj18.mm"
include "cfv.mm"
include "cop.mm"
include "dmeqi.mm"
include "dmun.mm"
include "fvex.mm"
include "dmsnop.mm"
include "uneq2i.mm"
include "3eqtri.mm"
include "uneq1d.mm"
include "uncom.mm"
include "syl6eq.mm"
include "syl5eq.mm"

theorem bnj1416
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  let bnjwtam: wff ta'
  assume bnj1416.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1416.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1416.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1416.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1416.5: |- D = { x e. A | -. E. f ta }
  assume bnj1416.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1416.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1416.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1416.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1416.10: |- P = U. H
  assume bnj1416.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1416.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1416.28: |- ( ch -> dom P = _trCl ( x , A , R ) )


  assert |- ( ch -> dom Q = ( { x } u. _trCl ( x , A , R ) ) )

  proof
    wch
    cQ
    cdm
    #
    cP
    cdm
    #
    vx
    cv
    #
    csn
    #
    cun
    #
    @3
    cA
    cR
    @2
    c-bnj18
    #
    cun
    #
    @0
    cP
    @2
    cZ
    cG
    cfv
    #
    cop
    csn
    #
    cun
    #
    cdm
    @1
    @8
    cdm
    #
    cun
    @4
    cQ
    @9
    bnj1416.12
    dmeqi
    cP
    @8
    dmun
    @10
    @3
    @1
    @2
    @7
    cZ
    cG
    fvex
    dmsnop
    uneq2i
    3eqtri
    wch
    @4
    @5
    @3
    cun
    @6
    wch
    @1
    @5
    @3
    bnj1416.28
    uneq1d
    @5
    @3
    uncom
    syl6eq
    syl5eq
end
