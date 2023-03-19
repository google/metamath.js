include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "w3a.mm"
include "cplusg.mm"
include "cof.mm"
include "wfun.mm"
include "csupp.mm"
include "cfn.mm"
include "wfn.mm"
include "elmapfn.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "adantl.mm"
include "simp1r.mm"
include "inidm.mm"
include "offn.mm"
include "fnfun.mm"
include "syl.mm"
include "id.mm"
include "fsuppimpd.mm"
include "anim12i.mm"
include "mndpsuppfi.mm"
include "syl3an3.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "fvexd.mm"
include "isfsupp.mm"
include "sylancr.mm"
include "mpbir2and.mm"

theorem mndpfsupp
  let cA: class A
  let cB: class B
  let cR: class R
  let cM: class M
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume mndpsuppfi.r: |- R = ( Base ` M )


  assert |- ( ( ( M e. Mnd /\ V e. X ) /\ ( A e. ( R ^m V ) /\ B e. ( R ^m V ) ) /\ ( A finSupp ( 0g ` M ) /\ B finSupp ( 0g ` M ) ) ) -> ( A oF ( +g ` M ) B ) finSupp ( 0g ` M ) )

  proof
    cM
    cmnd
    wcel
    #
    cV
    cX
    wcel
    #
    wa
    #
    cA
    cR
    cV
    cmap
    co
    #
    wcel
    #
    cB
    @3
    wcel
    #
    wa
    #
    cA
    cM
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    cB
    @7
    cfsupp
    wbr
    #
    wa
    #
    w3a
    #
    cA
    cB
    cM
    cplusg
    cfv
    #
    cof
    #
    co
    #
    @7
    cfsupp
    wbr
    #
    @14
    wfun
    #
    @14
    @7
    csupp
    co
    cfn
    wcel
    #
    @11
    @14
    cV
    wfn
    @16
    @11
    cV
    cV
    @12
    cV
    cA
    cB
    cX
    cX
    @6
    @2
    cA
    cV
    wfn
    #
    @10
    @4
    @18
    @5
    cA
    cR
    cV
    elmapfn
    adantr
    3ad2ant2
    @6
    @2
    cB
    cV
    wfn
    #
    @10
    @5
    @19
    @4
    cB
    cR
    cV
    elmapfn
    adantl
    3ad2ant2
    @0
    @1
    @6
    @10
    simp1r
    #
    @20
    cV
    inidm
    offn
    cV
    @14
    fnfun
    syl
    @10
    @2
    @6
    cA
    @7
    csupp
    co
    cfn
    wcel
    #
    cB
    @7
    csupp
    co
    cfn
    wcel
    #
    wa
    @17
    @8
    @21
    @9
    @22
    @8
    cA
    @7
    @8
    id
    fsuppimpd
    @9
    cB
    @7
    @9
    id
    fsuppimpd
    anim12i
    cA
    cB
    cR
    cM
    cV
    cX
    mndpsuppfi.r
    mndpsuppfi
    syl3an3
    @11
    @14
    cvv
    wcel
    @7
    cvv
    wcel
    @15
    @16
    @17
    wa
    wb
    cA
    cB
    @13
    ovex
    @11
    cM
    c0g
    fvexd
    @14
    cvv
    cvv
    @7
    isfsupp
    sylancr
    mpbir2and
end
