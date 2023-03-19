include "bicom1.mm"

theorem bisaiaisb
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ps <-> ph ) -> ( ph <-> ps ) )

  proof
    wps
    wph
    bicom1
end
