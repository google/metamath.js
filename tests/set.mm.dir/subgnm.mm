include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "cv.mm"
include "c0g.mm"
include "cds.mm"
include "co.mm"
include "cmpt.mm"
include "cres.mm"
include "eqid.mm"
include "subgss.mm"
include "resmptd.mm"
include "subgbas.mm"
include "ressds.mm"
include "eqidd.mm"
include "subg0.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "eqtr2d.mm"
include "nmfval.mm"
include "reseq1i.mm"
include "3eqtr4g.mm"

theorem subgnm
  let cA: class A
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume subgngp.h: |- H = ( G |`s A )
  assume subgnm.n: |- N = ( norm ` G )
  assume subgnm.m: |- M = ( norm ` H )


  assert |- ( A e. ( SubGrp ` G ) -> M = ( N |` A ) )

  proof
    cA
    cG
    csubg
    cfv
    #
    wcel
    #
    vx
    cH
    cbs
    cfv
    #
    vx
    cv
    #
    cH
    c0g
    cfv
    #
    cH
    cds
    cfv
    #
    co
    #
    cmpt
    #
    vx
    cG
    cbs
    cfv
    #
    @3
    cG
    c0g
    cfv
    #
    cG
    cds
    cfv
    #
    co
    #
    cmpt
    #
    cA
    cres
    #
    cM
    cN
    cA
    cres
    @1
    @13
    vx
    cA
    @11
    cmpt
    @7
    @1
    vx
    @8
    cA
    @11
    @8
    cA
    cG
    @8
    eqid
    #
    subgss
    resmptd
    @1
    vx
    cA
    @11
    @2
    @6
    cA
    cG
    cH
    subgngp.h
    subgbas
    @1
    @3
    @3
    @9
    @4
    @10
    @5
    cA
    @10
    cG
    cH
    @0
    subgngp.h
    @10
    eqid
    #
    ressds
    @1
    @3
    eqidd
    cA
    cG
    cH
    @9
    subgngp.h
    @9
    eqid
    #
    subg0
    oveq123d
    mpteq12dv
    eqtr2d
    vx
    @5
    cM
    cH
    @2
    @4
    subgnm.m
    @2
    eqid
    @4
    eqid
    @5
    eqid
    nmfval
    cN
    @12
    cA
    vx
    @10
    cN
    cG
    @8
    @9
    subgnm.n
    @14
    @16
    @15
    nmfval
    reseq1i
    3eqtr4g
end
