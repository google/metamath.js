include "cn0.mm"
include "wcel.mm"
include "zring.mm"
include "csn.mm"
include "crsp.mm"
include "cfv.mm"
include "cqg.mm"
include "co.mm"
include "cqus.mm"
include "czrh.mm"
include "cres.mm"
include "cle.mm"
include "ccom.mm"
include "ccnv.mm"
include "eqid.mm"
include "znle.mm"
include "znzrh.mm"
include "reseq1d.mm"
include "syl6eqr.mm"
include "coeq1d.mm"
include "cnveqd.mm"
include "coeq12d.mm"
include "eqtrd.mm"

theorem znle2
  let cF: class F
  let c.le: class .<_
  let cN: class N
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cX: class X
  let cB: class B
  assume znle2.y: |- Y = ( Z/nZ ` N )
  assume znle2.f: |- F = ( ( ZRHom ` Y ) |` W )
  assume znle2.w: |- W = if ( N = 0 , ZZ , ( 0 ..^ N ) )
  assume znle2.l: |- .<_ = ( le ` Y )


  assert |- ( N e. NN0 -> .<_ = ( ( F o. <_ ) o. `' F ) )

  proof
    cN
    cn0
    wcel
    #
    c.le
    zring
    zring
    cN
    csn
    zring
    crsp
    cfv
    #
    cfv
    cqg
    co
    cqus
    co
    #
    czrh
    cfv
    #
    cW
    cres
    #
    cle
    ccom
    #
    @4
    ccnv
    #
    ccom
    cF
    cle
    ccom
    #
    cF
    ccnv
    #
    ccom
    @1
    @2
    @4
    c.le
    cN
    cW
    cY
    @1
    eqid
    #
    @2
    eqid
    #
    znle2.y
    @4
    eqid
    znle2.w
    znle2.l
    znle
    @0
    @5
    @7
    @6
    @8
    @0
    @4
    cF
    cle
    @0
    @4
    cY
    czrh
    cfv
    #
    cW
    cres
    cF
    @0
    @3
    @11
    cW
    @1
    @2
    cN
    cY
    @9
    @10
    znle2.y
    znzrh
    reseq1d
    znle2.f
    syl6eqr
    #
    coeq1d
    @0
    @4
    cF
    @12
    cnveqd
    coeq12d
    eqtrd
end
