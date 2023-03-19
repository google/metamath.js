include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
include "ltexp2.mm"
include "syl31anc.mm"

theorem ltexp2d
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cN: class N
  assume resqcld.1: |- ( ph -> A e. RR )
  assume ltexp2d.2: |- ( ph -> M e. ZZ )
  assume ltexp2d.3: |- ( ph -> N e. ZZ )
  assume ltexp2d.4: |- ( ph -> 1 < A )


  assert |- ( ph -> ( M < N <-> ( A ^ M ) < ( A ^ N ) ) )

  proof
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
    cM
    cN
    clt
    wbr
    cA
    cM
    cexp
    co
    cA
    cN
    cexp
    co
    clt
    wbr
    wb
    resqcld.1
    ltexp2d.2
    ltexp2d.3
    ltexp2d.4
    cA
    cM
    cN
    ltexp2
    syl31anc
end
