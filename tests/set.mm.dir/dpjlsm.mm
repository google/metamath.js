include "cdprd.mm"
include "co.mm"
include "csn.mm"
include "cres.mm"
include "cdif.mm"
include "cfv.mm"
include "dprdf2.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjdif.mm"
include "a1i.mm"
include "cun.mm"
include "undif2.mm"
include "wss.mm"
include "snssd.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5req.mm"
include "dprdsplit.mm"
include "dpjlem.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem dpjlsm
  let wph: wff ph
  let c.po: class .(+)
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
  let cP: class P
  let cC: class C
  let cQ: class Q
  let cW: class W
  let cA: class A
  let cY: class Y
  assume dpjfval.1: |- ( ph -> G dom DProd S )
  assume dpjfval.2: |- ( ph -> dom S = I )
  assume dpjlem.3: |- ( ph -> X e. I )
  assume dpjlsm.s: |- .(+) = ( LSSum ` G )


  assert |- ( ph -> ( G DProd S ) = ( ( S ` X ) .(+) ( G DProd ( S |` ( I \ { X } ) ) ) ) )

  proof
    wph
    cG
    cS
    cdprd
    co
    cG
    cS
    cX
    csn
    #
    cres
    cdprd
    co
    #
    cG
    cS
    cI
    @0
    cdif
    #
    cres
    cdprd
    co
    #
    c.po
    co
    cX
    cS
    cfv
    #
    @3
    c.po
    co
    wph
    @0
    @2
    c.po
    cS
    cG
    cI
    wph
    cS
    cG
    cI
    dpjfval.1
    dpjfval.2
    dprdf2
    @0
    @2
    cin
    c0
    wceq
    wph
    @0
    cI
    disjdif
    a1i
    wph
    @0
    @2
    cun
    @0
    cI
    cun
    #
    cI
    @0
    cI
    undif2
    wph
    @0
    cI
    wss
    @5
    cI
    wceq
    wph
    cX
    cI
    dpjlem.3
    snssd
    @0
    cI
    ssequn1
    sylib
    syl5req
    dpjlsm.s
    dpjfval.1
    dprdsplit
    wph
    @1
    @4
    @3
    c.po
    wph
    cS
    cG
    cI
    cX
    dpjfval.1
    dpjfval.2
    dpjlem.3
    dpjlem
    oveq1d
    eqtrd
end
