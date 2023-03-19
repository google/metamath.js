include "wcel.mm"
include "wa.mm"
include "ctrlson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "cwlkson.mm"
include "ctrls.mm"
include "copab.mm"
include "trlsonfval.mm"
include "breqd.mm"
include "wceq.mm"
include "breq12.mm"
include "anbi12d.mm"
include "eqid.mm"
include "brabga.mm"
include "sylan9bb.mm"

theorem istrlson
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assume trlsonfval.v: |- V = ( Vtx ` G )


  assert |- ( ( ( A e. V /\ B e. V ) /\ ( F e. U /\ P e. Z ) ) -> ( F ( A ( TrailsOn ` G ) B ) P <-> ( F ( A ( WalksOn ` G ) B ) P /\ F ( Trails ` G ) P ) ) )

  proof
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    #
    cF
    cP
    cA
    cB
    cG
    ctrlson
    cfv
    co
    #
    wbr
    cF
    cP
    vf
    cv
    #
    vp
    cv
    #
    cA
    cB
    cG
    cwlkson
    cfv
    co
    #
    wbr
    #
    @2
    @3
    cG
    ctrls
    cfv
    #
    wbr
    #
    wa
    #
    vf
    vp
    copab
    #
    wbr
    cF
    cU
    wcel
    cP
    cZ
    wcel
    wa
    cF
    cP
    @4
    wbr
    #
    cF
    cP
    @6
    wbr
    #
    wa
    #
    @0
    @1
    @9
    cF
    cP
    cA
    cB
    vf
    cG
    cV
    vp
    trlsonfval.v
    trlsonfval
    breqd
    @8
    @12
    vf
    vp
    cF
    cP
    @9
    cU
    cZ
    @2
    cF
    wceq
    @3
    cP
    wceq
    wa
    @5
    @10
    @7
    @11
    @2
    cF
    @3
    cP
    @4
    breq12
    @2
    cF
    @3
    cP
    @6
    breq12
    anbi12d
    @9
    eqid
    brabga
    sylan9bb
end
