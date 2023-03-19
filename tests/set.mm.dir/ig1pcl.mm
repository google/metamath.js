include "cdr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c0g.mm"
include "csn.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "wne.mm"
include "w3a.mm"
include "cmn1.mm"
include "cdg1.mm"
include "cdif.mm"
include "cima.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "eqid.mm"
include "ig1pval3.mm"
include "simp1d.mm"
include "3expa.mm"
include "crg.mm"
include "drngring.mm"
include "ig1pval2.mm"
include "syl.mm"
include "fvex.mm"
include "elsn.mm"
include "sylibr.mm"
include "adantr.mm"
include "pm2.61ne.mm"

theorem ig1pcl
  let cP: class P
  let cR: class R
  let cU: class U
  let cG: class G
  let cI: class I
  assume ig1pval.p: |- P = ( Poly1 ` R )
  assume ig1pval.g: |- G = ( idlGen1p ` R )
  assume ig1pcl.u: |- U = ( LIdeal ` P )


  assert |- ( ( R e. DivRing /\ I e. U ) -> ( G ` I ) e. I )

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
    cI
    cG
    cfv
    #
    cI
    wcel
    #
    cP
    c0g
    cfv
    #
    csn
    #
    cG
    cfv
    #
    @5
    wcel
    #
    cI
    @5
    cI
    @5
    wceq
    #
    @2
    @6
    cI
    @5
    cI
    @5
    cG
    fveq2
    @8
    id
    eleq12d
    @0
    @1
    cI
    @5
    wne
    #
    @3
    @0
    @1
    @9
    w3a
    @3
    @2
    cR
    cmn1
    cfv
    #
    wcel
    @2
    cR
    cdg1
    cfv
    #
    cfv
    @11
    cI
    @5
    cdif
    cima
    cr
    clt
    cinf
    wceq
    @11
    cP
    cR
    cU
    cG
    cI
    @10
    @4
    ig1pval.p
    ig1pval.g
    @4
    eqid
    #
    ig1pcl.u
    @11
    eqid
    @10
    eqid
    ig1pval3
    simp1d
    3expa
    @0
    @7
    @1
    @0
    @6
    @4
    wceq
    #
    @7
    @0
    cR
    crg
    wcel
    @13
    cR
    drngring
    cP
    cR
    cG
    @4
    ig1pval.p
    ig1pval.g
    @12
    ig1pval2
    syl
    @6
    @4
    @5
    cG
    fvex
    elsn
    sylibr
    adantr
    pm2.61ne
end
