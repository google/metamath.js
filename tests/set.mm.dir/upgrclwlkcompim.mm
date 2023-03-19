include "cupgr.mm"
include "wcel.mm"
include "cclwlks.mm"
include "cfv.mm"
include "wa.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "clwlkcompim.mm"
include "adantl.mm"
include "simprl.mm"
include "cwlks.mm"
include "clwlkwlk.mm"
include "upgrwlkcompim.mm"
include "simp3d.mm"
include "sylan2.mm"
include "adantr.mm"
include "simprrr.mm"
include "3jca.mm"
include "mpdan.mm"

theorem upgrclwlkcompim
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  assume isclwlke.v: |- V = ( Vtx ` G )
  assume isclwlke.i: |- I = ( iEdg ` G )
  assume clwlkcomp.1: |- F = ( 1st ` W )
  assume clwlkcomp.2: |- P = ( 2nd ` W )

  disjoint F k
  disjoint G k
  disjoint P k
  disjoint I k
  disjoint V k
  disjoint G f
  disjoint G g
  disjoint f g
  disjoint W f
  disjoint W g
  assert |- ( ( G e. UPGraph /\ W e. ( ClWalks ` G ) ) -> ( ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V ) /\ A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } /\ ( P ` 0 ) = ( P ` ( # ` F ) ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cW
    cG
    cclwlks
    cfv
    wcel
    #
    wa
    #
    cF
    cI
    cdm
    cword
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    cV
    cP
    wf
    #
    wa
    #
    vk
    cv
    #
    cP
    cfv
    #
    @7
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @7
    cF
    cfv
    cI
    cfv
    #
    @8
    csn
    wceq
    @8
    @9
    cpr
    #
    @10
    wss
    wif
    vk
    cc0
    @4
    cfzo
    co
    #
    wral
    #
    cc0
    cP
    cfv
    @4
    cP
    cfv
    wceq
    #
    wa
    #
    wa
    #
    @6
    @10
    @11
    wceq
    vk
    @12
    wral
    #
    @14
    w3a
    @1
    @16
    @0
    cP
    vk
    cF
    cG
    cI
    cV
    cW
    isclwlke.v
    isclwlke.i
    clwlkcomp.1
    clwlkcomp.2
    clwlkcompim
    adantl
    @2
    @16
    wa
    @6
    @17
    @14
    @2
    @6
    @15
    simprl
    @2
    @17
    @16
    @1
    @0
    cW
    cG
    cwlks
    cfv
    wcel
    #
    @17
    cG
    cW
    clwlkwlk
    @0
    @18
    wa
    @3
    @5
    @17
    cP
    vk
    cF
    cG
    cI
    cV
    cW
    isclwlke.v
    isclwlke.i
    clwlkcomp.1
    clwlkcomp.2
    upgrwlkcompim
    simp3d
    sylan2
    adantr
    @2
    @6
    @13
    @14
    simprrr
    3jca
    mpdan
end
