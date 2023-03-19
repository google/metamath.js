include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "co.mm"
include "wi.mm"
include "simp3.mm"
include "lsmless12.mm"
include "ex.mm"
include "syl2anc.mm"
include "wceq.mm"
include "lsmidm.mm"
include "3ad2ant3.mm"
include "sseq2d.mm"
include "sylibd.mm"
include "lsmub1.mm"
include "3adant3.mm"
include "sstr2.mm"
include "syl.mm"
include "lsmub2.mm"
include "jcad.mm"
include "impbid.mm"

theorem lsmlub
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let va: setvar a
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let cR: class R
  assume lsmub1.p: |- .(+) = ( LSSum ` G )


  assert |- ( ( S e. ( SubGrp ` G ) /\ T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) -> ( ( S C_ U /\ T C_ U ) <-> ( S .(+) T ) C_ U ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cT
    @0
    wcel
    #
    cU
    @0
    wcel
    #
    w3a
    #
    cS
    cU
    wss
    #
    cT
    cU
    wss
    #
    wa
    #
    cS
    cT
    c.po
    co
    #
    cU
    wss
    #
    @4
    @7
    @8
    cU
    cU
    c.po
    co
    #
    wss
    #
    @9
    @4
    @3
    @3
    @7
    @11
    wi
    @1
    @2
    @3
    simp3
    #
    @12
    @3
    @3
    wa
    @7
    @11
    c.po
    cS
    cU
    cT
    cU
    cG
    lsmub1.p
    lsmless12
    ex
    syl2anc
    @4
    @10
    cU
    @8
    @3
    @1
    @10
    cU
    wceq
    @2
    c.po
    cU
    cG
    lsmub1.p
    lsmidm
    3ad2ant3
    sseq2d
    sylibd
    @4
    @9
    @5
    @6
    @4
    cS
    @8
    wss
    #
    @9
    @5
    wi
    @1
    @2
    @13
    @3
    c.po
    cS
    cT
    cG
    lsmub1.p
    lsmub1
    3adant3
    cS
    @8
    cU
    sstr2
    syl
    @4
    cT
    @8
    wss
    #
    @9
    @6
    wi
    @1
    @2
    @14
    @3
    c.po
    cS
    cT
    cG
    lsmub1.p
    lsmub2
    3adant3
    cT
    @8
    cU
    sstr2
    syl
    jcad
    impbid
end
