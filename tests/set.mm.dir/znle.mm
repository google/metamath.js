include "cn0.mm"
include "wcel.mm"
include "cple.mm"
include "cfv.mm"
include "cnx.mm"
include "cle.mm"
include "ccom.mm"
include "ccnv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "eqid.mm"
include "znval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "zring.mm"
include "csn.mm"
include "cqg.mm"
include "cqus.mm"
include "ovex.mm"
include "eqeltri.mm"
include "czrh.mm"
include "cres.mm"
include "fvex.mm"
include "resex.mm"
include "cxr.mm"
include "cxp.mm"
include "xrex.mm"
include "xpex.mm"
include "lerelxr.mm"
include "ssexi.mm"
include "coex.mm"
include "cnvex.mm"
include "pleid.mm"
include "setsid.mm"
include "mp2an.mm"
include "3eqtr4g.mm"

theorem znle
  let cS: class S
  let cU: class U
  let cF: class F
  let c.le: class .<_
  let cN: class N
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vn: setvar n
  let vs: setvar s
  let vz: setvar z
  assume znval.s: |- S = ( RSpan ` ZZring )
  assume znval.u: |- U = ( ZZring /s ( ZZring ~QG ( S ` { N } ) ) )
  assume znval.y: |- Y = ( Z/nZ ` N )
  assume znval.f: |- F = ( ( ZRHom ` U ) |` W )
  assume znval.w: |- W = if ( N = 0 , ZZ , ( 0 ..^ N ) )
  assume znle.l: |- .<_ = ( le ` Y )


  assert |- ( N e. NN0 -> .<_ = ( ( F o. <_ ) o. `' F ) )

  proof
    cN
    cn0
    wcel
    #
    cY
    cple
    cfv
    cU
    cnx
    cple
    cfv
    cF
    cle
    ccom
    #
    cF
    ccnv
    #
    ccom
    #
    cop
    csts
    co
    #
    cple
    cfv
    #
    c.le
    @3
    @0
    cY
    @4
    cple
    cS
    cU
    cF
    @3
    cN
    cW
    cY
    znval.s
    znval.u
    znval.y
    znval.f
    znval.w
    @3
    eqid
    znval
    fveq2d
    znle.l
    cU
    cvv
    wcel
    @3
    cvv
    wcel
    @3
    @5
    wceq
    cU
    zring
    zring
    cN
    csn
    cS
    cfv
    cqg
    co
    #
    cqus
    co
    cvv
    znval.u
    zring
    @6
    cqus
    ovex
    eqeltri
    @1
    @2
    cF
    cle
    cF
    cU
    czrh
    cfv
    #
    cW
    cres
    cvv
    znval.f
    @7
    cW
    cU
    czrh
    fvex
    resex
    eqeltri
    #
    cle
    cxr
    cxr
    cxp
    cxr
    cxr
    xrex
    xrex
    xpex
    lerelxr
    ssexi
    coex
    cF
    @8
    cnvex
    coex
    cvv
    @3
    cple
    cvv
    cU
    pleid
    setsid
    mp2an
    3eqtr4g
end
