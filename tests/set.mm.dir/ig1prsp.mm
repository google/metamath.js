include "cdr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "cdsr.mm"
include "wbr.mm"
include "wral.mm"
include "ig1pcl.mm"
include "eqid.mm"
include "ig1pdvds.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "crg.mm"
include "cbs.mm"
include "wb.mm"
include "drngring.mm"
include "ply1ring.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "wss.mm"
include "lidlss.mm"
include "adantl.mm"
include "sseldd.mm"
include "lidldvgen.mm"
include "syl3anc.mm"
include "mpbir2and.mm"

theorem ig1prsp
  let cP: class P
  let cR: class R
  let cU: class U
  let cG: class G
  let cI: class I
  let cK: class K
  let vx: setvar x
  assume ig1pval.p: |- P = ( Poly1 ` R )
  assume ig1pval.g: |- G = ( idlGen1p ` R )
  assume ig1pcl.u: |- U = ( LIdeal ` P )
  assume ig1prsp.k: |- K = ( RSpan ` P )


  assert |- ( ( R e. DivRing /\ I e. U ) -> I = ( K ` { ( G ` I ) } ) )

  proof
    cR
    cdr
    wcel
    #
    cI
    cU
    wcel
    #
    wa
    #
    cI
    cI
    cG
    cfv
    #
    csn
    cK
    cfv
    wceq
    #
    @3
    cI
    wcel
    #
    @3
    vx
    cv
    #
    cP
    cdsr
    cfv
    #
    wbr
    #
    vx
    cI
    wral
    #
    cP
    cR
    cU
    cG
    cI
    ig1pval.p
    ig1pval.g
    ig1pcl.u
    ig1pcl
    #
    @2
    @8
    vx
    cI
    @0
    @1
    @6
    cI
    wcel
    @8
    @7
    cP
    cR
    cU
    cG
    cI
    @6
    ig1pval.p
    ig1pval.g
    ig1pcl.u
    @7
    eqid
    #
    ig1pdvds
    3expa
    ralrimiva
    @2
    cP
    crg
    wcel
    #
    @1
    @3
    cP
    cbs
    cfv
    #
    wcel
    @4
    @5
    @9
    wa
    wb
    @0
    @12
    @1
    @0
    cR
    crg
    wcel
    @12
    cR
    drngring
    cP
    cR
    ig1pval.p
    ply1ring
    syl
    adantr
    @0
    @1
    simpr
    @2
    cI
    @13
    @3
    @1
    cI
    @13
    wss
    @0
    @13
    cI
    cU
    cP
    @13
    eqid
    #
    ig1pcl.u
    lidlss
    adantl
    @10
    sseldd
    vx
    @13
    @7
    cP
    cU
    @3
    cI
    cK
    @14
    ig1pcl.u
    ig1prsp.k
    @11
    lidldvgen
    syl3anc
    mpbir2and
end
