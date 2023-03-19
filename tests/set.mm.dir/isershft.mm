include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cshi.mm"
include "co.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "cmin.mm"
include "wceq.mm"
include "zaddcl.mm"
include "seqshft.mm"
include "sylancom.mm"
include "cc.mm"
include "zcn.mm"
include "pncan.mm"
include "syl2an.mm"
include "seqeq1d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "wb.mm"
include "cvv.mm"
include "seqex.mm"
include "climshft.mm"
include "mpan2.mm"
include "adantl.mm"
include "bitr2d.mm"

theorem isershft
  let cA: class A
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let cN: class N
  assume isershft.1: |- F e. _V


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( seq M ( .+ , F ) ~~> A <-> seq ( M + N ) ( .+ , ( F shift N ) ) ~~> A ) )

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
    c.pl
    cF
    cN
    cshi
    co
    cM
    cN
    caddc
    co
    #
    cseq
    #
    cA
    cli
    wbr
    c.pl
    cF
    cM
    cseq
    #
    cN
    cshi
    co
    #
    cA
    cli
    wbr
    #
    @5
    cA
    cli
    wbr
    #
    @2
    @4
    @6
    cA
    cli
    @2
    @4
    c.pl
    cF
    @3
    cN
    cmin
    co
    #
    cseq
    #
    cN
    cshi
    co
    #
    @6
    @0
    @1
    @3
    cz
    wcel
    @4
    @11
    wceq
    cM
    cN
    zaddcl
    c.pl
    cF
    @3
    cN
    isershft.1
    seqshft
    sylancom
    @2
    @10
    @5
    cN
    cshi
    @2
    @9
    cM
    c.pl
    cF
    @0
    cM
    cc
    wcel
    cN
    cc
    wcel
    @9
    cM
    wceq
    @1
    cM
    zcn
    cN
    zcn
    cM
    cN
    pncan
    syl2an
    seqeq1d
    oveq1d
    eqtrd
    breq1d
    @1
    @7
    @8
    wb
    #
    @0
    @1
    @5
    cvv
    wcel
    @12
    c.pl
    cF
    cM
    seqex
    cA
    @5
    cN
    cvv
    climshft
    mpan2
    adantl
    bitr2d
end
