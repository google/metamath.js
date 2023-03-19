include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cdprd.mm"
include "co.mm"
include "cpj1.mm"
include "clsm.mm"
include "cress.mm"
include "cghm.mm"
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
include "pj1ghm.mm"
include "dpjval.mm"
include "dpjlsm.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "3eltr4d.mm"

theorem dpjghm
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
  assume dpjlid.3: |- ( ph -> X e. I )


  assert |- ( ph -> ( P ` X ) e. ( ( G |`s ( G DProd S ) ) GrpHom G ) )

  proof
    wph
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
    cG
    @0
    @4
    cG
    clsm
    cfv
    #
    co
    #
    cress
    co
    #
    cG
    cghm
    co
    cX
    cP
    cfv
    cG
    cG
    cS
    cdprd
    co
    #
    cress
    co
    #
    cG
    cghm
    co
    wph
    @5
    cG
    cplusg
    cfv
    #
    @6
    @0
    @4
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
    @6
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
    dpjlid.3
    ffvelrnd
    wph
    cG
    @3
    cdprd
    cdm
    wbr
    #
    @4
    @17
    wcel
    wph
    @18
    @4
    @9
    wss
    wph
    @2
    cS
    cG
    cI
    dpjfval.1
    dpjfval.2
    wph
    cI
    @1
    difssd
    dprdres
    simpld
    @3
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
    dpjlid.3
    @16
    dpjcntz
    @5
    eqid
    #
    pj1ghm
    wph
    cP
    @5
    cS
    cG
    cI
    cX
    dpjfval.1
    dpjfval.2
    dpjfval.p
    @19
    dpjlid.3
    dpjval
    wph
    @10
    @8
    cG
    cghm
    wph
    @9
    @7
    cG
    cress
    wph
    @6
    cS
    cG
    cI
    cX
    dpjfval.1
    dpjfval.2
    dpjlid.3
    @14
    dpjlsm
    oveq2d
    oveq1d
    3eltr4d
end
