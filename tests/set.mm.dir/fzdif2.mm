include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "c1.mm"
include "cmin.mm"
include "cun.mm"
include "fzspl.mm"
include "difeq1d.mm"
include "difun2.mm"
include "syl6eq.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "cz.mm"
include "eluzelz.mm"
include "uzid.mm"
include "uznfz.mm"
include "3syl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "disjdif2.mm"
include "syl.mm"
include "eqtrd.mm"

theorem fzdif2
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( ( M ... N ) \ { N } ) = ( M ... ( N - 1 ) ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    cN
    cfz
    co
    #
    cN
    csn
    #
    cdif
    #
    cM
    cN
    c1
    cmin
    co
    cfz
    co
    #
    @2
    cdif
    #
    @4
    @0
    @3
    @4
    @2
    cun
    #
    @2
    cdif
    @5
    @0
    @1
    @6
    @2
    cM
    cN
    fzspl
    difeq1d
    @4
    @2
    difun2
    syl6eq
    @0
    @4
    @2
    cin
    c0
    wceq
    #
    @5
    @4
    wceq
    @0
    cN
    @4
    wcel
    wn
    #
    @7
    @0
    cN
    cz
    wcel
    cN
    cN
    cuz
    cfv
    wcel
    @8
    cM
    cN
    eluzelz
    cN
    uzid
    cN
    cM
    cN
    uznfz
    3syl
    @4
    cN
    disjsn
    sylibr
    @4
    @2
    disjdif2
    syl
    eqtrd
end
