include "cbits.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cn0.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "bitsval.mm"
include "df-3an.mm"
include "bitri.mm"
include "baib.mm"

theorem bitsval2
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vm: setvar m


  assert |- ( ( N e. ZZ /\ M e. NN0 ) -> ( M e. ( bits ` N ) <-> -. 2 || ( |_ ` ( N / ( 2 ^ M ) ) ) ) )

  proof
    cM
    cN
    cbits
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    c2
    cN
    c2
    cM
    cexp
    co
    cdiv
    co
    cfl
    cfv
    cdvds
    wbr
    wn
    #
    @0
    @1
    @2
    @4
    w3a
    @3
    @4
    wa
    cM
    cN
    bitsval
    @1
    @2
    @4
    df-3an
    bitri
    baib
end
