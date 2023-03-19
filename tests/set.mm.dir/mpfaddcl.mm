include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cpws.mm"
include "cplusg.mm"
include "cof.mm"
include "ccrg.mm"
include "cvv.mm"
include "eqid.mm"
include "csubrg.mm"
include "w3a.mm"
include "mpfrcl.mm"
include "adantr.mm"
include "simp2d.mm"
include "ovexd.mm"
include "wss.mm"
include "mpfsubrg.mm"
include "syl.mm"
include "subrgss.mm"
include "simpl.mm"
include "sseldd.mm"
include "simpr.mm"
include "pwsplusgval.mm"
include "subrgacl.mm"
include "3expib.mm"
include "mpcom.mm"
include "eqeltrrd.mm"

theorem mpfaddcl
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cI: class I
  assume mpfsubrg.q: |- Q = ran ( ( I evalSub S ) ` R )
  assume mpfaddcl.p: |- .+ = ( +g ` S )


  assert |- ( ( F e. Q /\ G e. Q ) -> ( F oF .+ G ) e. Q )

  proof
    cF
    cQ
    wcel
    #
    cG
    cQ
    wcel
    #
    wa
    #
    cF
    cG
    cS
    cS
    cbs
    cfv
    #
    cI
    cmap
    co
    #
    cpws
    co
    #
    cplusg
    cfv
    #
    co
    #
    cF
    cG
    c.pl
    cof
    co
    cQ
    @2
    @5
    cbs
    cfv
    #
    c.pl
    @6
    cS
    cF
    cG
    @4
    ccrg
    cvv
    @5
    @5
    eqid
    @8
    eqid
    #
    @2
    cI
    cvv
    wcel
    #
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    wcel
    #
    @0
    @10
    @11
    @12
    w3a
    #
    @1
    cQ
    cR
    cS
    cI
    cF
    mpfsubrg.q
    mpfrcl
    adantr
    #
    simp2d
    @2
    @3
    cI
    cmap
    ovexd
    @2
    cQ
    @8
    cF
    @2
    cQ
    @5
    csubrg
    cfv
    wcel
    #
    cQ
    @8
    wss
    @2
    @13
    @15
    @14
    cQ
    cR
    cS
    cI
    cvv
    mpfsubrg.q
    mpfsubrg
    syl
    #
    cQ
    @8
    @5
    @9
    subrgss
    syl
    #
    @0
    @1
    simpl
    sseldd
    @2
    cQ
    @8
    cG
    @17
    @0
    @1
    simpr
    sseldd
    mpfaddcl.p
    @6
    eqid
    #
    pwsplusgval
    @15
    @2
    @7
    cQ
    wcel
    #
    @16
    @15
    @0
    @1
    @19
    cQ
    @6
    @5
    cF
    cG
    @18
    subrgacl
    3expib
    mpcom
    eqeltrrd
end
