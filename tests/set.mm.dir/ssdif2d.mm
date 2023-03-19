include "cdif.mm"
include "sscond.mm"
include "ssdifd.mm"
include "sstrd.mm"

theorem ssdif2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ssdifd.1: |- ( ph -> A C_ B )
  assume ssdif2d.2: |- ( ph -> C C_ D )


  assert |- ( ph -> ( A \ D ) C_ ( B \ C ) )

  proof
    wph
    cA
    cD
    cdif
    cA
    cC
    cdif
    cB
    cC
    cdif
    wph
    cC
    cD
    cA
    ssdif2d.2
    sscond
    wph
    cA
    cB
    cC
    ssdifd.1
    ssdifd
    sstrd
end
