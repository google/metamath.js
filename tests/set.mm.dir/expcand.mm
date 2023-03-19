include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "expcan.mm"
include "syl31anc.mm"
include "mpbid.mm"

theorem expcand
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cN: class N
  assume resqcld.1: |- ( ph -> A e. RR )
  assume ltexp2d.2: |- ( ph -> M e. ZZ )
  assume ltexp2d.3: |- ( ph -> N e. ZZ )
  assume ltexp2d.4: |- ( ph -> 1 < A )
  assume expcand.5: |- ( ph -> ( A ^ M ) = ( A ^ N ) )


  assert |- ( ph -> M = N )

  proof
    wph
    cA
    cM
    cexp
    co
    cA
    cN
    cexp
    co
    wceq
    #
    cM
    cN
    wceq
    #
    expcand.5
    wph
    cA
    cr
    wcel
    cM
    cz
    wcel
    cN
    cz
    wcel
    c1
    cA
    clt
    wbr
    @0
    @1
    wb
    resqcld.1
    ltexp2d.2
    ltexp2d.3
    ltexp2d.4
    cA
    cM
    cN
    expcan
    syl31anc
    mpbid
end
