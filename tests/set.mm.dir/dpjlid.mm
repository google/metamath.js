include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cdprd.mm"
include "co.mm"
include "cpj1.mm"
include "eqid.mm"
include "dpjval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "cplusg.mm"
include "clsm.mm"
include "c0g.mm"
include "ccntz.mm"
include "csubg.mm"
include "dprdf2.mm"
include "ffvelrnd.mm"
include "cdm.mm"
include "wbr.mm"
include "wss.mm"
include "difssd.mm"
include "dprdres.mm"
include "simpld.mm"
include "dprdsubg.mm"
include "syl.mm"
include "dpjdisj.mm"
include "dpjcntz.mm"
include "pj1lid.mm"
include "mpdan.mm"
include "eqtrd.mm"

theorem dpjlid
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cX: class X
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let c.0: class .0.
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vs: setvar s
  let cC: class C
  let cQ: class Q
  let cW: class W
  let cY: class Y
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjfval.p: |- P = ( G dProj S )
  assume dpjlid.3: |- ( ph -> X e. I )
  assume dpjlid.4: |- ( ph -> A e. ( S ` X ) )


  assert |- ( ph -> ( ( P ` X ) ` A ) = A )

  proof
    wph
    cA
    cX
    cP
    cfv
    #
    cfv
    cA
    cX
    cS
    cfv
    #
    cG
    cS
    cI
    cX
    csn
    #
    cdif
    #
    cres
    #
    cdprd
    co
    #
    cG
    cpj1
    cfv
    #
    co
    #
    cfv
    #
    cA
    wph
    cA
    @0
    @7
    wph
    cP
    @6
    cS
    cG
    cI
    cX
    dpjfval.1
    dpjfval.2
    dpjfval.p
    @6
    eqid
    #
    dpjlid.3
    dpjval
    fveq1d
    wph
    cA
    @1
    wcel
    @8
    cA
    wceq
    dpjlid.4
    wph
    @6
    cG
    cplusg
    cfv
    #
    cG
    clsm
    cfv
    #
    @1
    @5
    cG
    cA
    cG
    c0g
    cfv
    #
    cG
    ccntz
    cfv
    #
    @10
    eqid
    @11
    eqid
    @12
    eqid
    #
    @13
    eqid
    #
    wph
    cI
    cG
    csubg
    cfv
    #
    cX
    cS
    wph
    cS
    cG
    cI
    dpjfval.1
    dpjfval.2
    dprdf2
    dpjlid.3
    ffvelrnd
    wph
    cG
    @4
    cdprd
    cdm
    wbr
    #
    @5
    @16
    wcel
    wph
    @17
    @5
    cG
    cS
    cdprd
    co
    wss
    wph
    @3
    cS
    cG
    cI
    dpjfval.1
    dpjfval.2
    wph
    cI
    @2
    difssd
    dprdres
    simpld
    @4
    cG
    dprdsubg
    syl
    wph
    cS
    cG
    cI
    cX
    @12
    dpjfval.1
    dpjfval.2
    dpjlid.3
    @14
    dpjdisj
    wph
    cS
    cG
    cI
    cX
    @13
    dpjfval.1
    dpjfval.2
    dpjlid.3
    @15
    dpjcntz
    @9
    pj1lid
    mpdan
    eqtrd
end
