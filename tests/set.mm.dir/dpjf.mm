include "cdprd.mm"
include "co.mm"
include "cfv.mm"
include "wf.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "clsm.mm"
include "cpj1.mm"
include "cplusg.mm"
include "c0g.mm"
include "ccntz.mm"
include "eqid.mm"
include "csubg.mm"
include "dprdf2.mm"
include "ffvelrnd.mm"
include "cdm.mm"
include "wbr.mm"
include "wcel.mm"
include "wss.mm"
include "difssd.mm"
include "dprdres.mm"
include "simpld.mm"
include "dprdsubg.mm"
include "syl.mm"
include "dpjdisj.mm"
include "dpjcntz.mm"
include "pj1f.mm"
include "dpjval.mm"
include "dpjlsm.mm"
include "feq12d.mm"
include "mpbird.mm"

theorem dpjf
  let wph: wff ph
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
  let cA: class A
  let cY: class Y
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjfval.p: |- P = ( G dProj S )
  assume dpjf.3: |- ( ph -> X e. I )


  assert |- ( ph -> ( P ` X ) : ( G DProd S ) --> ( S ` X ) )

  proof
    wph
    cG
    cS
    cdprd
    co
    #
    cX
    cS
    cfv
    #
    cX
    cP
    cfv
    #
    wf
    @1
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
    clsm
    cfv
    #
    co
    #
    @1
    @1
    @6
    cG
    cpj1
    cfv
    #
    co
    #
    wf
    wph
    @9
    cG
    cplusg
    cfv
    #
    @7
    @1
    @6
    cG
    cG
    c0g
    cfv
    #
    cG
    ccntz
    cfv
    #
    @11
    eqid
    @7
    eqid
    #
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
    dpjf.3
    ffvelrnd
    wph
    cG
    @5
    cdprd
    cdm
    wbr
    #
    @6
    @17
    wcel
    wph
    @18
    @6
    @0
    wss
    wph
    @4
    cS
    cG
    cI
    dpjfval.1
    dpjfval.2
    wph
    cI
    @3
    difssd
    dprdres
    simpld
    @5
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
    dpjf.3
    @15
    dpjdisj
    wph
    cS
    cG
    cI
    cX
    @13
    dpjfval.1
    dpjfval.2
    dpjf.3
    @16
    dpjcntz
    @9
    eqid
    #
    pj1f
    wph
    @0
    @8
    @1
    @2
    @10
    wph
    cP
    @9
    cS
    cG
    cI
    cX
    dpjfval.1
    dpjfval.2
    dpjfval.p
    @19
    dpjf.3
    dpjval
    wph
    @7
    cS
    cG
    cI
    cX
    dpjfval.1
    dpjfval.2
    dpjf.3
    @14
    dpjlsm
    feq12d
    mpbird
end
