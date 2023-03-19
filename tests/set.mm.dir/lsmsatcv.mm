include "wpss.mm"
include "co.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "cbs.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "clvec.mm"
include "wcel.mm"
include "eqid.mm"
include "islsati.mm"
include "syl2anc.mm"
include "w3a.mm"
include "adantr.mm"
include "simpr.mm"
include "lsmcv.mm"
include "3expib.mm"
include "3adant3.mm"
include "wb.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "anbi2d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "3impib.mm"

theorem lsmsatcv
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let vv: setvar v
  assume lsmsatcv.s: |- S = ( LSubSp ` W )
  assume lsmsatcv.p: |- .(+) = ( LSSum ` W )
  assume lsmsatcv.a: |- A = ( LSAtoms ` W )
  assume lsmsatcv.w: |- ( ph -> W e. LVec )
  assume lsmsatcv.t: |- ( ph -> T e. S )
  assume lsmsatcv.u: |- ( ph -> U e. S )
  assume lsmsatcv.x: |- ( ph -> Q e. A )


  assert |- ( ( ph /\ T C. U /\ U C_ ( T .(+) Q ) ) -> U = ( T .(+) Q ) )

  proof
    wph
    cT
    cU
    wpss
    #
    cU
    cT
    cQ
    c.po
    co
    #
    wss
    #
    cU
    @1
    wceq
    #
    wph
    cQ
    vv
    cv
    #
    csn
    cW
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    vv
    cW
    cbs
    cfv
    #
    wrex
    #
    @0
    @2
    wa
    #
    @3
    wi
    #
    wph
    cW
    clvec
    wcel
    #
    cQ
    cA
    wcel
    @9
    lsmsatcv.w
    lsmsatcv.x
    vv
    cA
    cQ
    @5
    @8
    cW
    clvec
    @8
    eqid
    #
    @5
    eqid
    #
    lsmsatcv.a
    islsati
    syl2anc
    wph
    @7
    @11
    vv
    @8
    wph
    @4
    @8
    wcel
    #
    @7
    w3a
    @11
    @0
    cU
    cT
    @6
    c.po
    co
    #
    wss
    #
    wa
    #
    cU
    @16
    wceq
    #
    wi
    #
    wph
    @15
    @20
    @7
    wph
    @15
    wa
    #
    @0
    @17
    @19
    @21
    c.po
    cS
    cT
    cU
    @5
    @8
    cW
    @4
    @13
    lsmsatcv.s
    @14
    lsmsatcv.p
    wph
    @12
    @15
    lsmsatcv.w
    adantr
    wph
    cT
    cS
    wcel
    @15
    lsmsatcv.t
    adantr
    wph
    cU
    cS
    wcel
    @15
    lsmsatcv.u
    adantr
    wph
    @15
    simpr
    lsmcv
    3expib
    3adant3
    @7
    wph
    @11
    @20
    wb
    @15
    @7
    @10
    @18
    @3
    @19
    @7
    @2
    @17
    @0
    @7
    @1
    @16
    cU
    cQ
    @6
    cT
    c.po
    oveq2
    #
    sseq2d
    anbi2d
    @7
    @1
    @16
    cU
    @22
    eqeq2d
    imbi12d
    3ad2ant3
    mpbird
    rexlimdv3a
    mpd
    3impib
end
