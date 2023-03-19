include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "cxp.mm"
include "wfn.mm"
include "wi.mm"
include "lmodscaf.mm"
include "ffnd.mm"
include "plusffn.mm"
include "wa.mm"
include "fneq1.mm"
include "fndmu.mm"
include "ex.mm"
include "syl6bi.mm"
include "com13.mm"
include "impcom.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "lmodbn0.mm"
include "xp11.mm"
include "syl2anc.mm"
include "simprbda.mm"
include "expcom.mm"
include "syl6.mm"
include "com23.mm"
include "ax-mp.mm"
include "mpd.mm"
include "imp.mm"

theorem lmodfopnelem1
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cK: class K
  let cV: class V
  let cW: class W
  assume lmodfopne.t: |- .x. = ( .sf ` W )
  assume lmodfopne.a: |- .+ = ( +f ` W )
  assume lmodfopne.v: |- V = ( Base ` W )
  assume lmodfopne.s: |- S = ( Scalar ` W )
  assume lmodfopne.k: |- K = ( Base ` S )


  assert |- ( ( W e. LMod /\ .+ = .x. ) -> V = K )

  proof
    cW
    clmod
    wcel
    #
    c.pl
    c.x
    wceq
    #
    cV
    cK
    wceq
    #
    @0
    c.x
    cK
    cV
    cxp
    #
    wfn
    #
    @1
    @2
    wi
    #
    @0
    @3
    cV
    c.x
    cV
    c.x
    cS
    cK
    cW
    lmodfopne.v
    lmodfopne.s
    lmodfopne.k
    lmodfopne.t
    lmodscaf
    ffnd
    c.pl
    cV
    cV
    cxp
    #
    wfn
    #
    @0
    @4
    @5
    wi
    wi
    cV
    c.pl
    cW
    lmodfopne.v
    lmodfopne.a
    plusffn
    @7
    @4
    @0
    @5
    @7
    @4
    @0
    @5
    wi
    @7
    @4
    wa
    #
    @1
    @0
    @2
    @8
    @1
    @6
    @3
    wceq
    #
    @0
    @2
    wi
    @4
    @7
    @1
    @9
    wi
    @1
    @7
    @4
    @9
    @1
    @7
    c.x
    @6
    wfn
    #
    @4
    @9
    wi
    @6
    c.pl
    c.x
    fneq1
    @10
    @4
    @9
    @6
    @3
    c.x
    fndmu
    ex
    syl6bi
    com13
    impcom
    @0
    @9
    @2
    @0
    @9
    @2
    cV
    cV
    wceq
    #
    @0
    cV
    c0
    wne
    #
    @12
    @9
    @2
    @11
    wa
    wb
    cV
    cW
    lmodfopne.v
    lmodbn0
    #
    @13
    cV
    cV
    cK
    cV
    xp11
    syl2anc
    simprbda
    expcom
    syl6
    com23
    ex
    com23
    ax-mp
    mpd
    imp
end
