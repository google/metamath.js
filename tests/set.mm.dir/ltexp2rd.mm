include "crp.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
include "ltexp2r.mm"
include "syl31anc.mm"

theorem ltexp2rd
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cN: class N
  assume rpexpcld.1: |- ( ph -> A e. RR+ )
  assume rpexpcld.2: |- ( ph -> N e. ZZ )
  assume ltexp2rd.3: |- ( ph -> M e. ZZ )
  assume ltexp2rd.4: |- ( ph -> A < 1 )


  assert |- ( ph -> ( M < N <-> ( A ^ N ) < ( A ^ M ) ) )

  proof
    wph
    cA
    crp
    wcel
    cM
    cz
    wcel
    cN
    cz
    wcel
    cA
    c1
    clt
    wbr
    cM
    cN
    clt
    wbr
    cA
    cN
    cexp
    co
    cA
    cM
    cexp
    co
    clt
    wbr
    wb
    rpexpcld.1
    ltexp2rd.3
    rpexpcld.2
    ltexp2rd.4
    cA
    cM
    cN
    ltexp2r
    syl31anc
end
