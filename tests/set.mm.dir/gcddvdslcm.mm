include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "clcm.mm"
include "gcddvds.mm"
include "simpld.mm"
include "dvdslcm.mm"
include "wi.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "simpl.mm"
include "lcmcl.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem gcddvdslcm
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M gcd N ) || ( M lcm N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cN
    cgcd
    co
    #
    cM
    cdvds
    wbr
    #
    cM
    cM
    cN
    clcm
    co
    #
    cdvds
    wbr
    #
    @3
    @5
    cdvds
    wbr
    #
    @2
    @4
    @3
    cN
    cdvds
    wbr
    cM
    cN
    gcddvds
    simpld
    @2
    @6
    cN
    @5
    cdvds
    wbr
    cM
    cN
    dvdslcm
    simpld
    @2
    @3
    cz
    wcel
    @0
    @5
    cz
    wcel
    @4
    @6
    wa
    @7
    wi
    @2
    @3
    cM
    cN
    gcdcl
    nn0zd
    @0
    @1
    simpl
    @2
    @5
    cM
    cN
    lcmcl
    nn0zd
    @3
    cM
    @5
    dvdstr
    syl3anc
    mp2and
end
