include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cz.mm"
include "elfvdm.mm"
include "cpw.mm"
include "uzf.mm"
include "fdmi.mm"
include "syl6eleq.mm"

theorem eluzel2
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( N e. ( ZZ>= ` M ) -> M e. ZZ )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    cM
    cuz
    cdm
    cz
    cN
    cM
    cuz
    elfvdm
    cz
    cz
    cpw
    cuz
    uzf
    fdmi
    syl6eleq
end
